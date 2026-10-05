//! Dumping a run for the `must-viz` visualizer.
//!
//! [`TraceObserver`] is a [`Observer`] that records every explorer
//! callback as one JSON *step* carrying a full snapshot of the execution graph, producing
//! a single document shaped exactly per `must-viz/TRACE_FORMAT.md` (version 1) — the
//! contract shared with the `must-viz` renderer. [`dump`](TraceObserver::dump) writes that
//! document to any [`std::io::Write`] (a file, an in-memory buffer, a socket — anything
//! playing the "writer"/output-stream role).
//!
//! ```no_run
//! use must::event::Model;
//! use must::viz::TraceObserver;
//! use must::{explore, Config, Ctx, Program, System};
//!
//! let make = || {
//!     let mut sys = System::new();
//!     sys.add(|c: Ctx| async move { c.send(1, "hi", Model::P2p); });
//!     sys.add(|c: Ctx| async move { let _ = c.recv(|_| true).await; });
//!     sys
//! };
//! // Pin the program's true thread count so every snapshot carries all N thread lanes.
//! let obs = TraceObserver::new("my-protocol", make().num_threads());
//! explore(make, &obs, Config::default());
//! obs.dump_to_file("run.trace.json").unwrap();
//! ```
//!
//! # Design
//!
//! The observer is built for a parallel run with no added contention and a small memory
//! footprint:
//!
//! - **Sharded by worker.** Each worker thread appends to its *own* buffer, chosen by the
//!   same per-worker id [`CountingObserver`](crate::CountingObserver) uses. With at least
//!   as many shards as workers (the default), two workers never touch the same shard, so
//!   the per-shard lock is always uncontended — the hot path is a lock/serialize/unlock
//!   with no cross-thread traffic.
//! - **Streamed, not staged.** A callback serializes its step straight to compact JSON
//!   bytes in the shard buffer. Nothing intermediate is kept: no `serde`, no owned mirror
//!   structs, and — unlike [`RecordingObserver`](crate::RecordingObserver) — no clone of
//!   the graph. Memory is the size of the finished trace text, nothing more.
//! - Untimed labels retain the v1 shape. Explicitly timed labels add optional `window`
//!   (send) or `timing` (receive) metadata; see [`ReceiveTiming`].
//!
//! [`dump`](TraceObserver::dump) concatenates the shard buffers in worker order. A
//! single-threaded run (the default) therefore yields one clean depth-first log, exactly
//! what the renderer reconstructs the exploration tree from. A parallel run stays
//! well-formed and complete, but its steps interleave the workers' subtrees (the same
//! caveat [`RecordingObserver`](crate::RecordingObserver) carries) — run with
//! `Config { threads: 1, .. }` when you want the animation to read as one search.

use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::Mutex;

use crate::event::{EventId, Label, Model, ReceiveTiming, Tid, Window};
use crate::explorer::{Execution, ExecutionKind};
use crate::graph::ExecutionGraph;
use crate::observer::{default_shards, worker_id, Observer};

/// Trace format version this observer emits (`meta.version`); the `must-viz` reader rejects
/// any other value.
const VERSION: u32 = 1;

/// One worker's slice of the trace: the serialized steps it produced (each already
/// prefixed with a `,` separator) plus its per-kind tally. Written by a single worker on
/// the hot path and merged only at [`dump`](TraceObserver::dump) time.
///
/// Aligned to a cache line so two workers appending to adjacent shards never trigger false
/// sharing, mirroring [`CountingObserver`](crate::CountingObserver)'s shard layout.
#[repr(align(64))]
#[derive(Debug)]
struct Shard {
    inner: Mutex<ShardInner>,
}

#[derive(Debug, Default)]
struct ShardInner {
    /// Serialized steps for this shard, back to back. Every step is written with a leading
    /// `,` so the shards concatenate into a valid JSON array once the very first comma is
    /// dropped (see [`dump`](TraceObserver::dump)).
    buf: Vec<u8>,
    counts: Summary,
}

impl Shard {
    fn new() -> Self {
        Shard {
            inner: Mutex::new(ShardInner::default()),
        }
    }
}

/// Per-kind step counts, matching `must-viz`'s `summary` object and the semantics of
/// [`CountingObserver`](crate::CountingObserver). Summed across shards at dump time; the
/// `must-viz` reader checks these equal the per-kind step counts (spec rule 4).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    pub events_added: usize,
    pub rf_choices: usize,
    pub inconsistent: usize,
    pub backward_revisits: usize,
    pub revisits_rejected: usize,
    pub threads_blocked: usize,
    pub full: usize,
    pub blocked: usize,
    pub errors: usize,
}

impl Summary {
    fn merge(&mut self, o: &Summary) {
        self.events_added += o.events_added;
        self.rf_choices += o.rf_choices;
        self.inconsistent += o.inconsistent;
        self.backward_revisits += o.backward_revisits;
        self.revisits_rejected += o.revisits_rejected;
        self.threads_blocked += o.threads_blocked;
        self.full += o.full;
        self.blocked += o.blocked;
        self.errors += o.errors;
    }
}

/// A [`must::Observer`](crate::Observer) that dumps a whole `explore` run as a single
/// `must-viz` trace document (`must-viz/TRACE_FORMAT.md`, version 1).
///
/// Construct it with the verified program's name and its true thread count `N`, share it
/// across the run (callbacks take `&self`), then [`dump`](Self::dump) the trace. See the
/// [module docs](self) for the sharded, streaming design.
#[derive(Debug)]
pub struct TraceObserver {
    /// `meta.program`: a free-form human name of the verified program.
    program: String,
    /// `meta.num_threads`: the program's true thread count `N`. Every snapshot emits
    /// exactly this many thread lanes (empty arrays for threads with no events yet), so it
    /// must be `>=` any `g.num_threads()` seen — pass the program's real `N`
    /// (`Program::num_threads`), which is always a correct ceiling.
    num_threads: usize,
    shards: Vec<Shard>,
}

impl TraceObserver {
    /// A fresh observer for a run of `program` with `num_threads` threads, sized for the
    /// machine's parallelism (one shard per hardware thread) so a parallel `explore` never
    /// contends. Use [`with_shards`](Self::with_shards) to match a known worker count
    /// exactly.
    ///
    /// `num_threads` must be the program's true thread count (typically
    /// `Program::num_threads`): the spec requires every snapshot to carry exactly that many
    /// thread lanes, and it must not be smaller than any graph the run produces.
    pub fn new(program: impl Into<String>, num_threads: usize) -> Self {
        Self::with_shards(program, num_threads, default_shards())
    }

    /// A fresh observer with an explicit shard count (at least one). Match it to the
    /// `Config::threads` of the run so no two workers share a shard (hence never contend);
    /// [`new`](Self::new) picks a sensible default.
    pub fn with_shards(program: impl Into<String>, num_threads: usize, shards: usize) -> Self {
        TraceObserver {
            program: program.into(),
            num_threads,
            shards: (0..shards.max(1)).map(|_| Shard::new()).collect(),
        }
    }

    /// This thread's shard (`worker_id mod shard_count`), the one it appends steps to.
    fn shard(&self) -> &Shard {
        &self.shards[worker_id() % self.shards.len()]
    }

    /// Append one already-serialized step to this worker's shard and bump `count_of` on its
    /// tally. `write_step` receives the shard buffer with its leading `,` already emitted
    /// and appends the step object.
    fn record(&self, count_of: impl Fn(&mut Summary), write_step: impl Fn(&mut Vec<u8>)) {
        let mut sh = self.shard().inner.lock().unwrap();
        count_of(&mut sh.counts);
        sh.buf.push(b',');
        write_step(&mut sh.buf);
    }

    /// Sum every shard's per-kind tally — the trace's `summary` object.
    pub fn summary(&self) -> Summary {
        let mut total = Summary::default();
        for shard in &self.shards {
            total.merge(&shard.inner.lock().unwrap().counts);
        }
        total
    }

    /// Write the whole trace, as compact JSON, to `w` (a file, an in-memory buffer, a
    /// socket — any [`std::io::Write`]). The bytes are exactly the `must-viz` v1 shape.
    ///
    /// Call this after `explore` returns (every worker has joined, so the shards are
    /// complete). It streams the header, then each shard's buffer in worker order, then the
    /// summary — no extra copy of the trace is built.
    pub fn dump<W: Write>(&self, mut w: W) -> io::Result<()> {
        // Header + meta. num_threads / summary are written as plain decimals; the
        // free-form strings are JSON-escaped.
        let mut header = Vec::new();
        header.extend_from_slice(br#"{"version":"#);
        push_uint(&mut header, VERSION as u64);
        header.extend_from_slice(br#","meta":{"program":"#);
        push_json_str(&mut header, &self.program);
        header.extend_from_slice(br#","num_threads":"#);
        push_uint(&mut header, self.num_threads as u64);
        header.extend_from_slice(br#","generator":"#);
        push_json_str(&mut header, &generator());
        header.extend_from_slice(br#"},"steps":["#);
        w.write_all(&header)?;

        // Steps: concatenate the shards in worker order. Each stored step carries a leading
        // `,`; drop only the first one across the whole array so the separators stay valid.
        let mut wrote_any = false;
        for shard in &self.shards {
            let inner = shard.inner.lock().unwrap();
            if inner.buf.is_empty() {
                continue;
            }
            if wrote_any {
                w.write_all(&inner.buf)?;
            } else {
                // Skip this shard's leading comma — it opens the array.
                w.write_all(&inner.buf[1..])?;
                wrote_any = true;
            }
        }

        // Summary.
        let s = self.summary();
        let mut tail = Vec::new();
        tail.extend_from_slice(br#"],"summary":{"#);
        write_summary(&mut tail, &s);
        tail.extend_from_slice(b"}}");
        w.write_all(&tail)
    }

    /// Write the trace, compactly, to the file at `path` (created or truncated), through a
    /// [`BufWriter`].
    pub fn dump_to_file<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        let mut w = BufWriter::new(File::create(path)?);
        self.dump(&mut w)?;
        w.flush()
    }

    /// The trace as an owned `String` (convenience for tests and small runs; prefer
    /// [`dump`](Self::dump) for large ones). Infallible: writing to a `Vec<u8>` never
    /// errors and the content is UTF-8 by construction.
    pub fn dump_to_string(&self) -> String {
        let mut buf = Vec::new();
        self.dump(&mut buf)
            .expect("writing a trace to a Vec never fails");
        String::from_utf8(buf).expect("the trace is valid UTF-8 by construction")
    }
}

/// `meta.generator`: the tool and version that produced the trace.
fn generator() -> String {
    format!("{} {}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"))
}

impl Observer for TraceObserver {
    fn on_event_added(&self, g: &ExecutionGraph, e: EventId) {
        self.record(
            |c| c.events_added += 1,
            |buf| {
                buf.extend_from_slice(br#"{"kind":"event_added","e":"#);
                push_eid(buf, e);
                push_graph_field(buf, g, self.num_threads);
                buf.push(b'}');
            },
        );
    }

    fn on_rf_choice(&self, g: &ExecutionGraph, r: EventId, src: Option<EventId>) {
        self.record(
            |c| c.rf_choices += 1,
            |buf| {
                buf.extend_from_slice(br#"{"kind":"rf_choice","r":"#);
                push_eid(buf, r);
                buf.extend_from_slice(br#","src":"#);
                push_opt_eid(buf, src);
                push_graph_field(buf, g, self.num_threads);
                buf.push(b'}');
            },
        );
    }

    fn on_inconsistent(&self, g: &ExecutionGraph) {
        self.record(
            |c| c.inconsistent += 1,
            |buf| {
                buf.extend_from_slice(br#"{"kind":"inconsistent""#);
                push_graph_field(buf, g, self.num_threads);
                buf.push(b'}');
            },
        );
    }

    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        deleted: &std::collections::BTreeSet<EventId>,
    ) {
        self.record(
            |c| c.backward_revisits += 1,
            |buf| {
                // `g` is the pre-restriction graph (revisit.rs calls this before
                // `restrict`), so every `deleted` event — including the revisiting send `s`,
                // which survives — is still present in this snapshot, exactly as the spec's
                // "backward_revisit" semantics require.
                buf.extend_from_slice(br#"{"kind":"backward_revisit","r":"#);
                push_eid(buf, r);
                buf.extend_from_slice(br#","s":"#);
                push_eid(buf, s);
                buf.extend_from_slice(br#","deleted":["#);
                let mut first = true;
                for &d in deleted {
                    if !first {
                        buf.push(b',');
                    }
                    first = false;
                    push_eid(buf, d);
                }
                buf.push(b']');
                push_graph_field(buf, g, self.num_threads);
                buf.push(b'}');
            },
        );
    }

    fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
        self.record(
            |c| c.revisits_rejected += 1,
            |buf| {
                buf.extend_from_slice(br#"{"kind":"revisit_rejected","r":"#);
                push_eid(buf, r);
                buf.extend_from_slice(br#","s":"#);
                push_eid(buf, s);
                push_graph_field(buf, g, self.num_threads);
                buf.push(b'}');
            },
        );
    }

    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        let g = exec.graph();
        self.record(
            |c| match kind {
                ExecutionKind::Full => c.full += 1,
                ExecutionKind::Blocked => c.blocked += 1,
                ExecutionKind::Error => c.errors += 1,
            },
            |buf| {
                buf.extend_from_slice(br#"{"kind":"execution","exec":"#);
                buf.extend_from_slice(match kind {
                    ExecutionKind::Full => br#""full""#,
                    ExecutionKind::Blocked => br#""blocked""#,
                    ExecutionKind::Error => br#""error""#,
                });
                push_graph_field(buf, g, self.num_threads);
                buf.push(b'}');
            },
        );
    }

    fn on_thread_blocked(&self, g: &ExecutionGraph, tid: Tid) {
        self.record(
            |c| c.threads_blocked += 1,
            |buf| {
                buf.extend_from_slice(br#"{"kind":"thread_blocked","tid":"#);
                push_uint(buf, tid as u64);
                push_graph_field(buf, g, self.num_threads);
                buf.push(b'}');
            },
        );
    }
}

// -- JSON writers ------------------------------------------------------------------
//
// Compact, allocation-light encoders matching serde_json's compact output byte for byte
// (same escape set, no space, non-ASCII passed through), so a trace from this observer is
// indistinguishable from one the standalone `must-trace` crate produced.

/// `,"graph":{"threads":[ ... ]}` — a full snapshot of `g` per the spec's "Graph" section:
/// exactly `num_threads` lanes (empty arrays for threads with no events yet), each event in
/// program order.
fn push_graph_field(buf: &mut Vec<u8>, g: &ExecutionGraph, num_threads: usize) {
    debug_assert!(
        g.num_threads() <= num_threads,
        "graph has {} threads but the trace was pinned to {num_threads}; pass the program's true N",
        g.num_threads()
    );
    buf.extend_from_slice(br#","graph":{"threads":["#);
    for t in 0..num_threads {
        if t > 0 {
            buf.push(b',');
        }
        buf.push(b'[');
        // Threads the graph has not grown to yet contribute an empty lane.
        let len = if t < g.num_threads() {
            g.thread_len(t)
        } else {
            0
        };
        for i in 0..len {
            if i > 0 {
                buf.push(b',');
            }
            push_event(buf, g, EventId::new(t, i));
        }
        buf.push(b']');
    }
    buf.extend_from_slice(b"]}");
}

/// One graph event: `{"label":{..},"stamp":N}` plus, per the spec, `"rf"` on every recv
/// (present, `null` = ⊥) and `"chosen"` on every nondet (present, `null` = not yet picked),
/// and neither on sends/errors.
fn push_event(buf: &mut Vec<u8>, g: &ExecutionGraph, e: EventId) {
    let label = g.label(e);
    buf.extend_from_slice(br#"{"label":"#);
    push_label(buf, label);
    buf.extend_from_slice(br#","stamp":"#);
    push_uint(buf, g.stamp(e));
    match label {
        Label::Recv { .. } => {
            buf.extend_from_slice(br#","rf":"#);
            push_opt_eid(buf, g.reads_from(e));
        }
        Label::Nondet { .. } => {
            buf.extend_from_slice(br#","chosen":"#);
            match g.nd_value(e) {
                Some(v) => push_json_str(buf, crate::intern::resolve(*v)),
                None => buf.extend_from_slice(b"null"),
            }
        }
        Label::Send { .. } | Label::Error { .. } => {}
    }
    buf.push(b'}');
}

/// An event label, tagged by `"type"` (spec "Label"). Field order matches the spec's
/// examples so the bytes read the same.
fn push_label(buf: &mut Vec<u8>, label: &Label) {
    match label {
        Label::Send {
            model,
            dst,
            val,
            window,
        } => {
            buf.extend_from_slice(br#"{"type":"send","model":"#);
            push_json_str(buf, model_str(*model));
            buf.extend_from_slice(br#","dst":"#);
            push_uint(buf, *dst as u64);
            buf.extend_from_slice(br#","val":"#);
            push_json_str(buf, crate::intern::resolve(*val));
            if !window.is_untimed() {
                buf.extend_from_slice(br#","window":"#);
                push_window(buf, *window);
            }
            buf.push(b'}');
        }
        Label::Recv {
            pred,
            blocking,
            timing,
        } => {
            buf.extend_from_slice(br#"{"type":"recv","pred":"#);
            push_json_str(buf, pred.repr());
            buf.extend_from_slice(br#","blocking":"#);
            buf.extend_from_slice(if *blocking { b"true" } else { b"false" });
            if let Some(window) = timing.window() {
                buf.extend_from_slice(br#","timing":{"mode":"#);
                push_json_str(
                    buf,
                    match timing {
                        ReceiveTiming::Timeout(_) => "timeout",
                        ReceiveTiming::Poll(_) => "poll",
                        ReceiveTiming::Abstract => unreachable!(),
                    },
                );
                buf.extend_from_slice(br#","window":"#);
                push_window(buf, window);
                buf.push(b'}');
            }
            buf.push(b'}');
        }
        Label::Nondet { set } => {
            buf.extend_from_slice(br#"{"type":"nondet","set":["#);
            for (i, v) in set.iter().enumerate() {
                if i > 0 {
                    buf.push(b',');
                }
                push_json_str(buf, crate::intern::resolve(*v));
            }
            buf.extend_from_slice(b"]}");
        }
        Label::Error { msg } => {
            buf.extend_from_slice(br#"{"type":"error","msg":"#);
            push_json_str(buf, msg);
            buf.push(b'}');
        }
    }
}

fn push_window(buf: &mut Vec<u8>, window: Window) {
    buf.extend_from_slice(br#"{"lo":"#);
    push_uint(buf, window.lo());
    buf.extend_from_slice(br#","hi":"#);
    match window.hi() {
        Some(hi) => push_uint(buf, hi),
        None => buf.extend_from_slice(b"null"),
    }
    buf.push(b'}');
}

/// The nine `summary` counters, in the spec's field order.
fn write_summary(buf: &mut Vec<u8>, s: &Summary) {
    let fields: [(&[u8], usize); 9] = [
        (b"events_added", s.events_added),
        (b"rf_choices", s.rf_choices),
        (b"inconsistent", s.inconsistent),
        (b"backward_revisits", s.backward_revisits),
        (b"revisits_rejected", s.revisits_rejected),
        (b"threads_blocked", s.threads_blocked),
        (b"full", s.full),
        (b"blocked", s.blocked),
        (b"errors", s.errors),
    ];
    for (i, (name, count)) in fields.into_iter().enumerate() {
        if i > 0 {
            buf.push(b',');
        }
        buf.push(b'"');
        buf.extend_from_slice(name);
        buf.extend_from_slice(br#"":"#);
        push_uint(buf, count as u64);
    }
}

fn model_str(m: Model) -> &'static str {
    match m {
        Model::Asyn => "asyn",
        Model::P2p => "p2p",
        Model::Cd => "cd",
        Model::Mbox => "mbox",
    }
}

/// An event id as `[tid, idx]`.
fn push_eid(buf: &mut Vec<u8>, e: EventId) {
    buf.push(b'[');
    push_uint(buf, e.tid as u64);
    buf.push(b',');
    push_uint(buf, e.idx as u64);
    buf.push(b']');
}

/// An optional event id: `[tid, idx]` or `null` (⊥ / no source).
fn push_opt_eid(buf: &mut Vec<u8>, e: Option<EventId>) {
    match e {
        Some(e) => push_eid(buf, e),
        None => buf.extend_from_slice(b"null"),
    }
}

/// A non-negative integer in decimal, without allocating.
fn push_uint(buf: &mut Vec<u8>, mut n: u64) {
    if n == 0 {
        buf.push(b'0');
        return;
    }
    // u64::MAX is 20 digits.
    let mut tmp = [0u8; 20];
    let mut i = tmp.len();
    while n > 0 {
        i -= 1;
        tmp[i] = b'0' + (n % 10) as u8;
        n /= 10;
    }
    buf.extend_from_slice(&tmp[i..]);
}

/// A JSON string literal, escaping exactly the set `serde_json` escapes: `"`, `\`, the
/// named control chars (`\b \t \n \f \r`), and any other `< 0x20` as `\u00XX`. Bytes
/// `>= 0x80` pass through verbatim (valid UTF-8, never split — we iterate the original
/// `&str`'s bytes), so non-ASCII payloads round-trip unchanged, matching serde_json.
fn push_json_str(buf: &mut Vec<u8>, s: &str) {
    buf.push(b'"');
    let bytes = s.as_bytes();
    let mut start = 0;
    for (i, &b) in bytes.iter().enumerate() {
        let escape: &[u8] = match b {
            b'"' => b"\\\"",
            b'\\' => b"\\\\",
            0x08 => b"\\b",
            0x09 => b"\\t",
            0x0a => b"\\n",
            0x0c => b"\\f",
            0x0d => b"\\r",
            0x00..=0x1f => {
                // Other control chars: \u00XX (two lowercase hex digits, as serde_json).
                buf.extend_from_slice(&bytes[start..i]);
                buf.extend_from_slice(b"\\u00");
                buf.push(hex_digit(b >> 4));
                buf.push(hex_digit(b & 0x0f));
                start = i + 1;
                continue;
            }
            _ => continue,
        };
        buf.extend_from_slice(&bytes[start..i]);
        buf.extend_from_slice(escape);
        start = i + 1;
    }
    buf.extend_from_slice(&bytes[start..]);
    buf.push(b'"');
}

fn hex_digit(n: u8) -> u8 {
    match n {
        0..=9 => b'0' + n,
        _ => b'a' + (n - 10),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uint_roundtrips() {
        for n in [0u64, 1, 9, 10, 99, 100, 12345, u64::MAX] {
            let mut buf = Vec::new();
            push_uint(&mut buf, n);
            assert_eq!(String::from_utf8(buf).unwrap(), n.to_string());
        }
    }

    #[test]
    fn json_string_escapes_match_serde_set() {
        let cases = [
            ("plain", r#""plain""#),
            ("a\"b", r#""a\"b""#),
            ("a\\b", r#""a\\b""#),
            ("tab\tnl\ncr\r", r#""tab\tnl\ncr\r""#),
            // Real control chars U+0000 and U+001F escape to \u00XX (lowercase hex).
            ("\u{0000}\u{001f}", "\"\\u0000\\u001f\""),
            ("unção", "\"unção\""), // non-ASCII passes through unescaped
        ];
        for (input, want) in cases {
            let mut buf = Vec::new();
            push_json_str(&mut buf, input);
            assert_eq!(String::from_utf8(buf).unwrap(), want, "escaping {input:?}");
        }
    }

    #[test]
    fn empty_run_is_a_well_formed_empty_trace() {
        let obs = TraceObserver::new("empty", 2);
        let s = obs.dump_to_string();
        // `VERSION` stands in for the crate version so a version bump never breaks this.
        let want = r#"{"version":1,"meta":{"program":"empty","num_threads":2,"generator":"must-mc VERSION"},"steps":[],"summary":{"events_added":0,"rf_choices":0,"inconsistent":0,"backward_revisits":0,"revisits_rejected":0,"threads_blocked":0,"full":0,"blocked":0,"errors":0}}"#
            .replace("VERSION", env!("CARGO_PKG_VERSION"));
        assert_eq!(s, want);
    }
}
