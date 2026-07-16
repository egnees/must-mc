//! Conformance + thread-safety tests for [`must::viz::TraceObserver`].
//!
//! The library is dependency-free, so these tests carry their own tiny (std-only) JSON
//! parser and an independent re-check of every rule in `must-viz/TRACE_FORMAT.md`
//! (version 1). That validator is written against the *spec*, not against the observer's
//! encoder, so a bug shared between the two could not hide — exactly the guarantee the
//! standalone `must-trace` crate got from validating with `serde_json::Value`.

use std::collections::BTreeSet;

use must::event::Model;
use must::viz::TraceObserver;
use must::{explore, Config, CountingObserver, Ctx, Program, System};

// ===================================================================================
// A minimal, std-only JSON value + parser (enough for trace documents).
// ===================================================================================

#[derive(Clone, Debug, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(fields) => fields.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    fn as_arr(&self) -> Option<&[Json]> {
        match self {
            Json::Arr(a) => Some(a),
            _ => None,
        }
    }
    /// A non-negative integer stored as a JSON number.
    fn as_uint(&self) -> Option<u64> {
        match self {
            Json::Num(n) if *n >= 0.0 && n.fract() == 0.0 => Some(*n as u64),
            _ => None,
        }
    }
}

struct Parser<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Parser<'a> {
    fn parse(s: &'a str) -> Json {
        let mut p = Parser {
            b: s.as_bytes(),
            i: 0,
        };
        p.ws();
        let v = p.value();
        p.ws();
        assert_eq!(p.i, p.b.len(), "trailing bytes after JSON value");
        v
    }

    fn ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }

    fn value(&mut self) -> Json {
        match self.b[self.i] {
            b'{' => self.object(),
            b'[' => self.array(),
            b'"' => Json::Str(self.string()),
            b't' => {
                self.expect(b"true");
                Json::Bool(true)
            }
            b'f' => {
                self.expect(b"false");
                Json::Bool(false)
            }
            b'n' => {
                self.expect(b"null");
                Json::Null
            }
            _ => self.number(),
        }
    }

    fn expect(&mut self, lit: &[u8]) {
        assert_eq!(&self.b[self.i..self.i + lit.len()], lit, "expected literal");
        self.i += lit.len();
    }

    fn object(&mut self) -> Json {
        self.i += 1; // {
        let mut fields = Vec::new();
        self.ws();
        if self.b[self.i] == b'}' {
            self.i += 1;
            return Json::Obj(fields);
        }
        loop {
            self.ws();
            let key = self.string();
            self.ws();
            assert_eq!(self.b[self.i], b':', "expected ':'");
            self.i += 1;
            self.ws();
            let val = self.value();
            fields.push((key, val));
            self.ws();
            match self.b[self.i] {
                b',' => self.i += 1,
                b'}' => {
                    self.i += 1;
                    break;
                }
                c => panic!("expected ',' or '}}' in object, got {}", c as char),
            }
        }
        Json::Obj(fields)
    }

    fn array(&mut self) -> Json {
        self.i += 1; // [
        let mut items = Vec::new();
        self.ws();
        if self.b[self.i] == b']' {
            self.i += 1;
            return Json::Arr(items);
        }
        loop {
            self.ws();
            items.push(self.value());
            self.ws();
            match self.b[self.i] {
                b',' => self.i += 1,
                b']' => {
                    self.i += 1;
                    break;
                }
                c => panic!("expected ',' or ']' in array, got {}", c as char),
            }
        }
        Json::Arr(items)
    }

    fn string(&mut self) -> String {
        assert_eq!(self.b[self.i], b'"', "expected string");
        self.i += 1;
        let mut out = String::new();
        loop {
            let c = self.b[self.i];
            self.i += 1;
            match c {
                b'"' => break,
                b'\\' => {
                    let e = self.b[self.i];
                    self.i += 1;
                    match e {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{0008}'),
                        b'f' => out.push('\u{000c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let hex = std::str::from_utf8(&self.b[self.i..self.i + 4]).unwrap();
                            let cp = u32::from_str_radix(hex, 16).unwrap();
                            self.i += 4;
                            out.push(char::from_u32(cp).unwrap());
                        }
                        _ => panic!("bad escape \\{}", e as char),
                    }
                }
                // Multi-byte UTF-8 passes through verbatim.
                _ => {
                    let start = self.i - 1;
                    let len = utf8_len(c);
                    let s = std::str::from_utf8(&self.b[start..start + len]).unwrap();
                    out.push_str(s);
                    self.i = start + len;
                }
            }
        }
        out
    }

    fn number(&mut self) -> Json {
        let start = self.i;
        while self.i < self.b.len()
            && matches!(
                self.b[self.i],
                b'0'..=b'9' | b'-' | b'+' | b'.' | b'e' | b'E'
            )
        {
            self.i += 1;
        }
        let s = std::str::from_utf8(&self.b[start..self.i]).unwrap();
        Json::Num(s.parse().unwrap())
    }
}

fn utf8_len(lead: u8) -> usize {
    match lead {
        0x00..=0x7f => 1,
        0xc0..=0xdf => 2,
        0xe0..=0xef => 3,
        _ => 4,
    }
}

// ===================================================================================
// Independent validator against TRACE_FORMAT.md v1.
// ===================================================================================

/// Per-kind step tally, in the spec's summary field order.
#[derive(Debug, Default, PartialEq, Eq)]
struct Counts {
    events_added: usize,
    rf_choices: usize,
    inconsistent: usize,
    backward_revisits: usize,
    revisits_rejected: usize,
    threads_blocked: usize,
    full: usize,
    blocked: usize,
    errors: usize,
}

/// Parse `json`, re-check every TRACE_FORMAT.md v1 rule, and return the (validated) step
/// count so callers can assert coverage. Panics with a rule reference on any violation.
fn validate(json: &str) -> usize {
    let root = Parser::parse(json);

    // Rule 1: version == 1.
    assert_eq!(
        root.get("version").and_then(Json::as_uint),
        Some(1),
        "rule 1: version"
    );

    let meta = root.get("meta").expect("meta present");
    assert!(
        meta.get("program").and_then(Json::as_str).is_some(),
        "meta.program is a string"
    );
    let n = meta
        .get("num_threads")
        .and_then(Json::as_uint)
        .expect("meta.num_threads uint") as usize;
    assert!(
        meta.get("generator").and_then(Json::as_str).is_some(),
        "meta.generator is a string"
    );

    let steps = root
        .get("steps")
        .and_then(Json::as_arr)
        .expect("steps array");
    let mut counts = Counts::default();

    for (si, step) in steps.iter().enumerate() {
        let kind = step
            .get("kind")
            .and_then(Json::as_str)
            .unwrap_or_else(|| panic!("step {si}: kind"));
        let graph = step
            .get("graph")
            .unwrap_or_else(|| panic!("step {si}: graph"));
        let threads = graph
            .get("threads")
            .and_then(Json::as_arr)
            .unwrap_or_else(|| panic!("step {si}: graph.threads"));

        // Rule 6: exactly num_threads lanes.
        assert_eq!(
            threads.len(),
            n,
            "rule 6 (step {si}): every snapshot carries all N thread lanes"
        );

        // Structural checks over every event + collect stamps and a (send?/recv?) map.
        let mut stamps = BTreeSet::new();
        let is_send = |t: usize, i: usize| -> Option<bool> {
            let ev = threads.get(t)?.as_arr()?.get(i)?;
            Some(ev.get("label")?.get("type")?.as_str()? == "send")
        };
        let is_recv = |t: usize, i: usize| -> bool {
            threads
                .get(t)
                .and_then(Json::as_arr)
                .and_then(|a| a.get(i))
                .and_then(|ev| ev.get("label"))
                .and_then(|l| l.get("type"))
                .and_then(Json::as_str)
                == Some("recv")
        };
        let exists = |t: usize, i: usize| -> bool {
            threads
                .get(t)
                .and_then(Json::as_arr)
                .map(|a| i < a.len())
                .unwrap_or(false)
        };

        for (t, lane) in threads.iter().enumerate() {
            let evs = lane
                .as_arr()
                .unwrap_or_else(|| panic!("step {si}: thread {t} not an array"));
            for (i, ev) in evs.iter().enumerate() {
                let stamp = ev
                    .get("stamp")
                    .and_then(Json::as_uint)
                    .unwrap_or_else(|| panic!("step {si} ⟨{t},{i}⟩: stamp"));
                assert!(
                    stamps.insert(stamp),
                    "step {si}: stamp {stamp} appears twice (stamps unique within a snapshot)"
                );
                let ty = ev
                    .get("label")
                    .and_then(|l| l.get("type"))
                    .and_then(Json::as_str)
                    .unwrap_or_else(|| panic!("step {si} ⟨{t},{i}⟩: label.type"));
                let has_rf = ev.get("rf").is_some();
                let has_chosen = ev.get("chosen").is_some();
                match ty {
                    "recv" => {
                        assert!(
                            has_rf && !has_chosen,
                            "step {si} ⟨{t},{i}⟩: recv carries rf, not chosen"
                        );
                        // Rule 2 + 3: rf target exists and is a send.
                        if let Some(rf) = ev.get("rf") {
                            if *rf != Json::Null {
                                let (rt, ri) = read_eid(rf);
                                assert!(
                                    exists(rt, ri),
                                    "rule 2 (step {si}): rf target ⟨{rt},{ri}⟩ exists"
                                );
                                assert_eq!(
                                    is_send(rt, ri),
                                    Some(true),
                                    "rule 3 (step {si}): rf target is a send"
                                );
                            }
                        }
                        // recv label shape.
                        let label = ev.get("label").unwrap();
                        assert!(
                            label.get("pred").and_then(Json::as_str).is_some(),
                            "recv.pred string"
                        );
                        assert!(
                            matches!(label.get("blocking"), Some(Json::Bool(_))),
                            "recv.blocking bool"
                        );
                    }
                    "nondet" => {
                        assert!(
                            has_chosen && !has_rf,
                            "step {si} ⟨{t},{i}⟩: nondet carries chosen, not rf"
                        );
                        let set = ev
                            .get("label")
                            .unwrap()
                            .get("set")
                            .and_then(Json::as_arr)
                            .expect("nondet.set array");
                        assert!(
                            set.iter().all(|v| v.as_str().is_some()),
                            "nondet.set is strings"
                        );
                    }
                    "send" => {
                        assert!(
                            !has_rf && !has_chosen,
                            "step {si} ⟨{t},{i}⟩: send carries neither rf nor chosen"
                        );
                        let label = ev.get("label").unwrap();
                        let model = label
                            .get("model")
                            .and_then(Json::as_str)
                            .expect("send.model");
                        assert!(
                            ["asyn", "p2p", "cd", "mbox"].contains(&model),
                            "send.model in enum"
                        );
                        assert!(
                            label.get("dst").and_then(Json::as_uint).is_some(),
                            "send.dst uint"
                        );
                        assert!(
                            label.get("val").and_then(Json::as_str).is_some(),
                            "send.val string"
                        );
                    }
                    "error" => {
                        assert!(
                            !has_rf && !has_chosen,
                            "step {si} ⟨{t},{i}⟩: error carries neither rf nor chosen"
                        );
                        assert!(
                            ev.get("label")
                                .unwrap()
                                .get("msg")
                                .and_then(Json::as_str)
                                .is_some(),
                            "error.msg string"
                        );
                    }
                    other => panic!("step {si} ⟨{t},{i}⟩: unknown label type {other:?}"),
                }
            }
        }

        // Kind-specific reference rules (2 + 3) and tallying.
        let check_eid_send = |name: &str, v: &Json| {
            let (t, i) = read_eid(v);
            assert!(exists(t, i), "rule 2 (step {si}): {name} ⟨{t},{i}⟩ exists");
            assert_eq!(
                is_send(t, i),
                Some(true),
                "rule 3 (step {si}): {name} is a send"
            );
        };
        let check_eid_recv = |name: &str, v: &Json| {
            let (t, i) = read_eid(v);
            assert!(exists(t, i), "rule 2 (step {si}): {name} ⟨{t},{i}⟩ exists");
            assert!(is_recv(t, i), "rule 3 (step {si}): {name} is a recv");
        };
        match kind {
            "event_added" => {
                let (t, i) = read_eid(step.get("e").expect("e"));
                assert!(exists(t, i), "rule 2 (step {si}): e ⟨{t},{i}⟩ exists");
                counts.events_added += 1;
            }
            "rf_choice" => {
                check_eid_recv("r", step.get("r").expect("r"));
                let src = step.get("src").expect("src");
                if *src != Json::Null {
                    check_eid_send("src", src);
                }
                counts.rf_choices += 1;
            }
            "inconsistent" => counts.inconsistent += 1,
            "backward_revisit" => {
                check_eid_recv("r", step.get("r").expect("r"));
                check_eid_send("s", step.get("s").expect("s"));
                for d in step
                    .get("deleted")
                    .and_then(Json::as_arr)
                    .expect("deleted array")
                {
                    let (t, i) = read_eid(d);
                    assert!(
                        exists(t, i),
                        "rule 2 (step {si}): deleted ⟨{t},{i}⟩ present pre-restriction"
                    );
                }
                counts.backward_revisits += 1;
            }
            "revisit_rejected" => {
                check_eid_recv("r", step.get("r").expect("r"));
                check_eid_send("s", step.get("s").expect("s"));
                counts.revisits_rejected += 1;
            }
            "execution" => {
                let exec = step.get("exec").and_then(Json::as_str).expect("exec");
                match exec {
                    "full" => counts.full += 1,
                    "blocked" => counts.blocked += 1,
                    "error" => counts.errors += 1,
                    other => panic!("step {si}: bad exec {other:?}"),
                }
            }
            "thread_blocked" => {
                let tid = step.get("tid").and_then(Json::as_uint).expect("tid") as usize;
                assert!(tid < n, "step {si}: tid {tid} in 0..{n}");
                counts.threads_blocked += 1;
            }
            other => panic!("step {si}: unknown kind {other:?}"),
        }
    }

    // Rule 4: summary equals the per-kind step counts.
    let sum = root.get("summary").expect("summary");
    let got = |k: &str| {
        sum.get(k)
            .and_then(Json::as_uint)
            .unwrap_or_else(|| panic!("summary.{k}")) as usize
    };
    let actual = Counts {
        events_added: got("events_added"),
        rf_choices: got("rf_choices"),
        inconsistent: got("inconsistent"),
        backward_revisits: got("backward_revisits"),
        revisits_rejected: got("revisits_rejected"),
        threads_blocked: got("threads_blocked"),
        full: got("full"),
        blocked: got("blocked"),
        errors: got("errors"),
    };
    assert_eq!(
        actual, counts,
        "rule 4: summary must equal per-kind step counts"
    );

    steps.len()
}

fn read_eid(v: &Json) -> (usize, usize) {
    let a = v.as_arr().expect("EventId is a two-element array");
    assert_eq!(a.len(), 2, "EventId is [tid, idx]");
    (
        a[0].as_uint().unwrap() as usize,
        a[1].as_uint().unwrap() as usize,
    )
}

// ===================================================================================
// Test programs.
// ===================================================================================

/// s+s+r: `T0: send(2,"1") ∥ T1: send(2,"2") ∥ T2: recv()`. Under priorities [0,2,1] the
/// send from T1 backward-revisits T2's receive.
fn ssr() -> System {
    let mut sys = System::new();
    sys.add(|c: Ctx| async move {
        c.send(2, "1", Model::P2p);
    });
    sys.add(|c: Ctx| async move {
        c.send(2, "2", Model::P2p);
    });
    sys.add(|c: Ctx| async move {
        let _ = c.recv(|_| true).await;
    });
    sys
}

/// A ⊥-reading non-blocking receive plus a blocking receive that never gets a message:
/// exercises `thread_blocked` and a `blocked` execution.
fn bottom_and_blocked() -> System {
    let mut sys = System::new();
    sys.add(|c: Ctx| async move {
        c.send(1, "ping", Model::P2p);
    });
    sys.add(|c: Ctx| async move {
        let _ = c.recv_timeout(|_| true).await;
    });
    sys.add(|c: Ctx| async move {
        let _ = c.recv(|_| true).await;
    }); // no send targets T2
    sys
}

/// A nondet choice guarded by an assertion: choosing `"bad"` reaches an `error`, `"ok"`
/// runs to `full`. Exercises `nondet` (with `chosen`) and `error`/`execution` kinds.
fn nondet_and_error() -> System {
    let mut sys = System::new();
    sys.add(|c: Ctx| async move {
        let v = c.nondet(["ok", "bad"]).await;
        c.assert_that(v == "ok", "nondet chose bad");
    });
    sys.add(|c: Ctx| async move {
        c.send(0, "hello", Model::P2p);
    });
    sys
}

fn dump(make: impl Fn() -> System + Sync, cfg: Config) -> (String, TraceObserver) {
    let n = make().num_threads();
    let obs = TraceObserver::new("test", n);
    explore(make, &obs, cfg);
    (obs.dump_to_string(), obs)
}

// ===================================================================================
// Tests.
// ===================================================================================

#[test]
fn ssr_trace_validates_and_covers_revisit() {
    let (json, _) = dump(ssr, Config::default().with_priorities(vec![0, 2, 1]));
    let steps = validate(&json);
    assert!(steps > 0);
    // The whole point of [0,2,1] is a backward revisit and two full executions.
    assert!(
        json.contains(r#""kind":"backward_revisit""#),
        "expected a backward revisit step"
    );
    assert!(json.contains(r#""kind":"event_added""#));
    assert!(json.contains(r#""kind":"rf_choice""#));
    assert!(json.contains(r#""kind":"execution","exec":"full""#));
}

#[test]
fn ssr_trace_is_byte_exact() {
    // Freeze the *whole* populated document byte-for-byte (field order, separators, the
    // pre-restriction `backward_revisit` snapshot, the trailing `inconsistent` step): the
    // format must stay identical, not merely structurally valid. The fixture carries a
    // `GENERATOR` placeholder so a version bump doesn't churn it.
    let obs = TraceObserver::new("s+s+r", ssr().num_threads());
    explore(ssr, &obs, Config::default().with_priorities(vec![0, 2, 1]));
    let got = obs.dump_to_string();

    let want = include_str!("fixtures/ssr.trace.json")
        .trim_end() // the file ends with a newline from generation; the dump does not
        .replace("GENERATOR", env!("CARGO_PKG_VERSION"));
    assert_eq!(
        got, want,
        "ssr trace must match the frozen byte-exact fixture"
    );
}

#[test]
fn bottom_and_blocked_trace_validates() {
    let (json, _) = dump(bottom_and_blocked, Config::default());
    validate(&json);
    assert!(
        json.contains(r#""kind":"thread_blocked""#),
        "expected a thread_blocked step"
    );
    assert!(
        json.contains(r#""kind":"execution","exec":"blocked""#),
        "expected a blocked execution"
    );
    assert!(
        json.contains(r#""blocking":false"#),
        "the recv_timeout is non-blocking"
    );
}

#[test]
fn nondet_and_error_trace_validates() {
    let (json, _) = dump(nondet_and_error, Config::default().collect_errors());
    validate(&json);
    assert!(
        json.contains(r#""type":"nondet""#),
        "expected a nondet event"
    );
    assert!(
        json.contains(r#""chosen":null"#),
        "the fresh nondet snapshot shows chosen:null"
    );
    assert!(
        json.contains(r#""kind":"execution","exec":"error""#),
        "expected an error execution"
    );
    assert!(json.contains(r#""type":"error","msg":"nondet chose bad""#));
}

#[test]
fn dump_apis_agree() {
    let n = ssr().num_threads();
    let obs = TraceObserver::new("apis", n);
    explore(ssr, &obs, Config::default().with_priorities(vec![0, 2, 1]));

    let via_string = obs.dump_to_string();
    let mut via_writer = Vec::new();
    obs.dump(&mut via_writer).unwrap();
    assert_eq!(
        via_string.as_bytes(),
        &via_writer[..],
        "dump and dump_to_string agree byte-for-byte"
    );

    let path =
        std::env::temp_dir().join(format!("must-viz-test-{}.trace.json", std::process::id()));
    obs.dump_to_file(&path).unwrap();
    let from_file = std::fs::read(&path).unwrap();
    std::fs::remove_file(&path).ok();
    assert_eq!(via_writer, from_file, "dump_to_file agrees byte-for-byte");
}

#[test]
fn summary_matches_counting_observer() {
    // Compose the trace observer with a CountingObserver over the same run (the crate's
    // tuple `Observer` impl fans every callback to both).
    let n = ssr().num_threads();
    let both = (TraceObserver::new("counts", n), CountingObserver::new());
    explore(ssr, &both, Config::default().with_priorities(vec![0, 2, 1]));
    let (obs, counting) = both;

    let s = obs.summary();
    assert_eq!(s.events_added, counting.events_added());
    assert_eq!(s.rf_choices, counting.rf_choices());
    assert_eq!(s.inconsistent, counting.inconsistent());
    assert_eq!(s.backward_revisits, counting.backward_revisits());
    assert_eq!(s.revisits_rejected, counting.revisits_rejected());
    assert_eq!(s.threads_blocked, counting.threads_blocked());
    assert_eq!(s.full, counting.full());
    assert_eq!(s.blocked, counting.blocked());
    assert_eq!(s.errors, counting.errors());
}

#[test]
fn parallel_run_is_well_formed_and_complete() {
    // The set of callbacks a parallel run makes equals the sequential run's (only their
    // order differs), so every summary counter must match — and the parallel dump must
    // still validate as a well-formed trace.
    let cfg_seq = Config::default().with_priorities(vec![0, 2, 1]);
    let (_seq_json, seq) = dump(ssr, cfg_seq);

    let n = ssr().num_threads();
    let par = TraceObserver::with_shards("par", n, 4);
    explore(
        ssr,
        &par,
        Config::default()
            .with_priorities(vec![0, 2, 1])
            .with_threads(4),
    );
    let par_json = par.dump_to_string();

    validate(&par_json);
    let (s, p) = (seq.summary(), par.summary());
    assert_eq!(
        s, p,
        "parallel and sequential runs see the same set of callbacks"
    );
}

#[test]
fn stress_many_shards_no_corruption() {
    // Far more workers than the tiny program needs, forcing shard reuse and interleaving;
    // the dump must still be a single well-formed JSON document.
    let n = ssr().num_threads();
    let obs = TraceObserver::with_shards("stress", n, 16);
    explore(ssr, &obs, Config::default().with_threads(16));
    validate(&obs.dump_to_string());
}
