//! Shared oracle helpers. Lives under `tests/common/` so it is *not* compiled as its own
//! test binary; each oracle file pulls it in with `mod common;`.
//!
//! The paper's benchmarks are all straight-line, value-independent programs, so a tiny
//! table-driven [`SeqProgram`] is the right vehicle: `next` advances purely by trace
//! length, no coroutine replay, so the large counters (ns+nr(8)=40320, ...) stay fast.
//! A handful of oracles are *also* built on the real `System` runtime (in the oracle
//! files themselves) to prove the runtime -> explorer path yields the same numbers.

// Each oracle crate uses a different subset of these helpers, so unused items are
// expected per-crate; silence the resulting dead-code warnings for the shared module.
#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};

use must::event::{EventId, Label, Model, Pred};
use must::{
    explore, Config, CountingObserver, ExecutionCollector, ExecutionGraph, Program, System,
    ThreadNext, Val,
};

/// A straight-line (value-independent) program: `threads[i]` is thread `i`'s ordered
/// event list. `next(traces)[i]` is the `(len+1)`-th event of thread `i`, where `len`
/// is how many of its events are already committed (`traces[i].len()`). Since control
/// flow never branches on received values, this needs no replay.
#[derive(Clone)]
pub struct SeqProgram {
    pub threads: Vec<Vec<Label>>,
}

impl Program for SeqProgram {
    fn num_threads(&self) -> usize {
        self.threads.len()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        self.threads
            .iter()
            .enumerate()
            .map(|(i, evs)| {
                let done = traces[i].len();
                if done < evs.len() {
                    ThreadNext::Next(evs[done].clone())
                } else {
                    ThreadNext::Finished
                }
            })
            .collect()
    }
    /// Straight-line control flow is trace-independent, so a thread's remaining events are
    /// exactly its remaining labels — an *exact* future for the forced-closure C1 rule.
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        let evs = &self.threads[tid];
        Some(evs[trace.len().min(evs.len())..].to_vec())
    }
}

impl SeqProgram {
    pub fn new(threads: Vec<Vec<Label>>) -> Self {
        SeqProgram { threads }
    }
}

// -- Label builders ---------------------------------------------------------------

pub fn send(model: Model, dst: usize, v: &str) -> Label {
    Label::send(model, dst, v)
}
/// Non-selective blocking receive (`recv(true)`).
pub fn recv() -> Label {
    Label::recv(Pred::any())
}
/// Selective blocking receive (`recv(|x| x == v)`).
pub fn recv_eq(v: &str) -> Label {
    Label::recv(Pred::eq(v))
}
/// Non-selective non-blocking receive (`recv_timeout(true)`) -- may read no message.
pub fn recv_nb() -> Label {
    Label::recv_nb(Pred::any())
}
/// Selective non-blocking receive (`recv_timeout(|x| x == v)`).
pub fn recv_nb_eq(v: &str) -> Label {
    Label::recv_nb(Pred::eq(v))
}
/// Data-nondeterminism `ND^S` over the option set `vals` (Algorithm 1 lines 6/19).
pub fn nondet(vals: &[&str]) -> Label {
    Label::nondet(vals.iter().copied())
}

// -- Oracle program builders (the paper's Table 1 benchmarks) ----------------------
//
// These were once inline in `tests/oracles.rs`; they moved here so the timed-filter
// tests can replay the whole oracle table under `Config::with_time_filter` without
// duplicating the constructions. The counts they assert are unchanged.

const P2P: Model = Model::P2p;

/// s+s+r: `T0: send(2,1) || T1: send(2,2) || T2: recv()` -- two senders to the receiver
/// (tid 2). The receive reads one of the two sends: 2 full executions.
pub fn ssr() -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(P2P, 2, "1")],
        vec![send(P2P, 2, "2")],
        vec![recv()],
    ])
}

/// ns+r(N): `T0..T(N-1): send(N, i) || TN: recv()`. N senders to the receiver (tid N),
/// one blocking receive that reads exactly one of them: N full executions (lazy
/// ordering -- N instead of N!).
pub fn ns_r(n: usize) -> SeqProgram {
    let mut threads: Vec<_> = (0..n).map(|i| vec![send(P2P, n, &i.to_string())]).collect();
    threads.push(vec![recv()]);
    SeqProgram::new(threads)
}

/// ns+nr(N): `T0..T(N-1): send(N, i) || TN: recv() ... recv()` (N receives). N sends
/// consumed by N non-selective receives in one thread: every permutation of the
/// delivery order is a distinct execution -- N! full executions.
pub fn ns_nr(n: usize) -> SeqProgram {
    let mut threads: Vec<_> = (0..n).map(|i| vec![send(P2P, n, &i.to_string())]).collect();
    threads.push((0..n).map(|_| recv()).collect());
    SeqProgram::new(threads)
}

/// ns+nr-sel(N): like ns+nr but the k-th receive is selective (`recv(x == k)`). Each
/// receive matches exactly one send, so there is a single consistent execution for any
/// N (selective receives collapse the N! down to 1).
pub fn ns_nr_sel(n: usize) -> SeqProgram {
    let mut threads: Vec<_> = (0..n).map(|i| vec![send(P2P, n, &i.to_string())]).collect();
    threads.push((0..n).map(|i| recv_eq(&i.to_string())).collect());
    SeqProgram::new(threads)
}

/// nworkers(N): main (tid 0) sends a message to *itself*, then receives; N workers
/// (tids 1..=N) each send to the coordinator (tid N+1); the coordinator receives all N
/// then sends "done" to main. The coordinator's N receives can consume the workers in
/// any order (N! ways) and main's receive may read either its own message or the
/// coordinator's (2 ways): 2*N! full executions (note the send-to-self).
pub fn nworkers(n: usize) -> SeqProgram {
    let coord = n + 1;
    let mut threads = vec![vec![send(P2P, 0, "self"), recv()]]; // main
    for w in 0..n {
        threads.push(vec![send(P2P, coord, &format!("w{w}"))]);
    }
    let mut coord_evs: Vec<_> = (0..n).map(|_| recv()).collect();
    coord_evs.push(send(P2P, 0, "done"));
    threads.push(coord_evs);
    SeqProgram::new(threads)
}

/// Example 2.8: `T1: send(T2,1); send(T2,2) || T2: recv(x==2); recv(x==1)`. Here the
/// paper's T-numbering is kept: `send(T2, ...)` targets tid 1 (the second, receiving
/// thread). Under p2p the two same-sender messages arrive in send order, so the only
/// consistent reading is the crossed one (2nd receive gets "1"): exactly 1 execution.
pub fn example_2_8() -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(P2P, 1, "1"), send(P2P, 1, "2")],
        vec![recv_eq("2"), recv_eq("1")],
    ])
}

/// Degenerate blocked oracle: `T0: send(1,"a") || T1: recv(x=="b")`. The predicate never
/// matches the only send, so there is no full execution and exactly one blocked one (the
/// receive is never added). Also checks the predicate participates in addability.
pub fn blocked_no_match() -> SeqProgram {
    SeqProgram::new(vec![vec![send(P2P, 1, "a")], vec![recv_eq("b")]])
}

/// Non-degenerate blocked oracle -- a program with both a full *and* a blocked terminal:
/// `T0: recv(); recv(x=="b") || T1: send(0,"a") || T2: send(0,"b")`. T0's first (any)
/// receive reads "a" or "b"; the second (`x=="b"`) needs "b".
///   * If the first reads "a", the second reads "b" -- a full execution.
///   * If the first reads "b", "b" is consumed, so the second `recv(x=="b")` has no
///     matching unread send and T0 blocks there -- a maximal consistent prefix.
///
/// So exactly 1 full + 1 blocked under every permutation.
pub fn blocked_and_full() -> SeqProgram {
    SeqProgram::new(vec![
        vec![recv(), recv_eq("b")],
        vec![send(P2P, 0, "a")],
        vec![send(P2P, 0, "b")],
    ])
}

// -- Combinatorics ----------------------------------------------------------------

pub fn factorial(n: usize) -> usize {
    (1..=n).product()
}

/// Every permutation of `0..n`. Only call for small `n` (`n!` grows fast); use
/// [`sample_perms`] for larger thread counts.
pub fn permutations(n: usize) -> Vec<Vec<usize>> {
    fn go(cur: &mut Vec<usize>, rest: &BTreeSet<usize>, out: &mut Vec<Vec<usize>>) {
        if rest.is_empty() {
            out.push(cur.clone());
            return;
        }
        for &x in rest {
            let mut r2 = rest.clone();
            r2.remove(&x);
            cur.push(x);
            go(cur, &r2, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    go(&mut Vec::new(), &(0..n).collect(), &mut out);
    out
}

/// A small, representative set of priority permutations for thread counts where
/// enumerating all `n!` would be wasteful: identity, reverse, and a rotation. Enough to
/// spot-check that execution counts and terminal-key sets are priority-invariant.
pub fn sample_perms(n: usize) -> Vec<Vec<usize>> {
    let id: Vec<usize> = (0..n).collect();
    let rev: Vec<usize> = (0..n).rev().collect();
    let mut rot: Vec<usize> = (1..n).collect();
    rot.push(0);
    let mut out = vec![id];
    if !out.contains(&rev) {
        out.push(rev);
    }
    if !out.contains(&rot) {
        out.push(rot);
    }
    out
}

// -- Running & assertions ---------------------------------------------------------

/// Run `prog` under an explicit priority permutation, collecting the terminal executions.
pub fn run(prog: &SeqProgram, perm: &[usize]) -> ExecutionCollector {
    let col = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &col,
        Config::default().with_priorities(perm.to_vec()),
    );
    col
}

/// No two terminal (full or blocked) executions share a canonical `(E, po, rf)` key --
/// the universal Theorem 4.1 "no duplicates" assertion.
pub fn assert_no_duplicates(col: &ExecutionCollector, ctx: &str) {
    let keys = col.terminal_keys();
    let unique: BTreeSet<&String> = keys.iter().collect();
    assert_eq!(
        keys.len(),
        unique.len(),
        "{ctx}: duplicate canonical keys among terminal executions:\n{keys:#?}"
    );
}

/// Core oracle assertion, starting from an explicit `base_cfg`. For every permutation in
/// `perms`, run `prog` under `base_cfg` with that permutation's priorities and require:
///   * `full_count == full`, `blocked_count == blocked`, `error_count == 0`;
///   * no duplicate terminal executions;
///   * the *set* of terminal canonical keys is identical across permutations
///     (execution equivalence classes are priority-independent -- completeness +
///     optimality of Must).
///
/// [`assert_oracle`] is the `Config::default()` case; passing a customised `base_cfg`
/// (e.g. one built with `with_time_filter`) lets a caller assert the same table under a
/// different configuration.
pub fn assert_oracle_cfg(
    name: &str,
    prog: &SeqProgram,
    perms: &[Vec<usize>],
    full: usize,
    blocked: usize,
    base_cfg: Config,
) {
    let mut reference: Option<BTreeSet<String>> = None;
    for perm in perms {
        let col = ExecutionCollector::new();
        explore(
            || prog.clone(),
            &col,
            base_cfg.clone().with_priorities(perm.to_vec()),
        );
        assert_eq!(
            col.full_count(),
            full,
            "{name} under priorities {perm:?}: full_count"
        );
        assert_eq!(
            col.blocked_count(),
            blocked,
            "{name} under priorities {perm:?}: blocked_count"
        );
        assert_eq!(
            col.error_count(),
            0,
            "{name} under priorities {perm:?}: error_count"
        );
        assert_no_duplicates(&col, name);

        let keyset: BTreeSet<String> = col.terminal_keys().into_iter().collect();
        match &reference {
            None => reference = Some(keyset),
            Some(r) => assert_eq!(
                &keyset, r,
                "{name}: terminal key set differs under priorities {perm:?} \
                 (executions must be priority-invariant)"
            ),
        }
    }
}

/// Core oracle assertion under `Config::default()`; see [`assert_oracle_cfg`].
pub fn assert_oracle(
    name: &str,
    prog: &SeqProgram,
    perms: &[Vec<usize>],
    full: usize,
    blocked: usize,
) {
    assert_oracle_cfg(name, prog, perms, full, blocked, Config::default());
}

/// Convenience: assert an oracle under the default `0..N` priorities only (for large
/// benchmarks where sweeping permutations is unnecessary).
pub fn assert_oracle_default(name: &str, prog: &SeqProgram, full: usize, blocked: usize) {
    let n = prog.num_threads();
    let id: Vec<usize> = (0..n).collect();
    assert_oracle(name, prog, &[id], full, blocked);
}

/// Timed-filter invariance (engine_plan §5.б.16): an all-untimed program is completely
/// unaffected by the eager time filter. Asserts the same `(full, blocked)` table, no
/// duplicates and priority invariance as [`assert_oracle`] — but under
/// `collect_errors().with_time_filter()` — and additionally that the filter suppressed
/// *nothing* (`filtered() == 0`), since every untimed send takes the `eager_feasible` fast
/// path (ahead of the Asyn/P2p-only model guard, so cd/mbox oracles are covered too).
pub fn assert_timed_invariant(
    name: &str,
    prog: &SeqProgram,
    perms: &[Vec<usize>],
    full: usize,
    blocked: usize,
) {
    // `with_time_filter` requires `collect_errors`; an all-untimed oracle has no error
    // events, so collect_errors leaves its counts identical to `Config::default`.
    let cfg = Config::default().collect_errors().with_time_filter();
    assert_oracle_cfg(name, prog, perms, full, blocked, cfg.clone());
    // Matching counts is necessary but not sufficient: assert the filter reported zero
    // suppressions directly (a CountingObserver, which assert_oracle_cfg does not use).
    for perm in perms {
        let counter = CountingObserver::new();
        explore(
            || prog.clone(),
            &counter,
            cfg.clone().with_priorities(perm.to_vec()),
        );
        assert_eq!(
            counter.filtered(),
            0,
            "{name} under priorities {perm:?}: untimed program had {} time-filtered terminals",
            counter.filtered()
        );
    }
}

// -- Independent eager-time realizability reference (engine_plan §0 / §5.в) -----------
//
// A from-scratch integer-enumeration oracle for the eager receive semantics, implemented
// straight from engine_plan §0 and deliberately NOT calling `must::time` — it is the
// differential reference the time filter is checked against (tests/timed.rs cross-checks,
// tests/fuzz_timed.rs corpus). Windows must be finite (the timed corpus, Б3).

/// Evaluator of the §0 clocks for one fixed integer delay vector `d` over a graph's sends.
struct TimeEval<'a> {
    g: &'a ExecutionGraph,
    send_idx: &'a BTreeMap<EventId, usize>,
    /// `d[send_idx[s]]` is the chosen integer delay of send `s` (within its window).
    d: &'a [i64],
    /// Memoised `fire` of each blocking receive (a pure function of `d`).
    fire: BTreeMap<EventId, i64>,
}

impl TimeEval<'_> {
    /// `Occ(e)`: fire of the last blocking receive po-before `e` in its thread, else 0.
    fn occ(&mut self, e: EventId) -> i64 {
        for idx in (0..e.idx).rev() {
            let p = EventId::new(e.tid, idx);
            if self.g.label(p).blocking() == Some(true) {
                return self.fire_of(p);
            }
        }
        0
    }

    /// `arr(s) = Occ(s) + d(s)`.
    fn arr(&mut self, s: EventId) -> i64 {
        self.occ(s) + self.d[self.send_idx[&s]]
    }

    /// `avail(s)`: for p2p, the max arrival over `s`'s channel prefix (FIFO reorder buffer);
    /// for asyn, just `arr(s)`.
    fn avail(&mut self, s: EventId) -> i64 {
        if self.g.send_model(s) == Some(Model::P2p) {
            let dst = self.g.label(s).dst();
            let mut m = i64::MIN;
            for idx in 0..=s.idx {
                let s2 = EventId::new(s.tid, idx);
                if self.g.send_model(s2) == Some(Model::P2p) && self.g.label(s2).dst() == dst {
                    let a = self.arr(s2);
                    m = m.max(a);
                }
            }
            m
        } else {
            self.arr(s)
        }
    }

    /// `fire(r) = max(Occ(r), avail(rf(r)))` (the coherent form; §0).
    fn fire_of(&mut self, r: EventId) -> i64 {
        if let Some(&v) = self.fire.get(&r) {
            return v;
        }
        let occ_r = self.occ(r);
        let v = match self.g.reads_from(r) {
            Some(s) => occ_r.max(self.avail(s)),
            None => occ_r, // a blocking recv reading ⊥ is absent from a consistent terminal
        };
        self.fire.insert(r, v);
        v
    }

    /// Whether every blocking receive's §0 A/B disjunction holds under this `d`.
    fn feasible(&mut self) -> bool {
        for r in self.g.recvs() {
            if self.g.label(r).blocking() != Some(true) {
                continue; // non-blocking receives are time-transparent
            }
            let Some(s) = self.g.reads_from(r) else {
                continue; // ⊥ (not present in a consistent terminal)
            };
            let occ_r = self.occ(r);
            let av_s = self.avail(s);
            // A: avail(rf) ≤ Occ(r) — accept, competitors NOT checked. Otherwise B requires
            // every competitor to be at-least-as-available as rf.
            if av_s <= occ_r {
                continue;
            }
            let competitors: Vec<EventId> = self
                .g
                .iter_sends()
                .filter(|&m| m != s && self.g.matches(m, r) && !consumed_before(self.g, m, r))
                .collect();
            for m in competitors {
                let av_m = self.avail(m);
                if av_m < av_s {
                    return false;
                }
            }
        }
        true
    }
}

/// Whether send `m` is consumed by the moment of blocking receive `r`: read by a receive
/// (of any kind, including non-blocking) po-earlier than `r` on `r`'s thread. Unread, or
/// read by a po-later receive, is *not* consumed — that is what makes it a competitor.
fn consumed_before(g: &ExecutionGraph, m: EventId, r: EventId) -> bool {
    match g.iter_recvs().find(|&r2| g.reads_from(r2) == Some(m)) {
        Some(r2) => r2.tid == r.tid && r2.idx < r.idx,
        None => false,
    }
}

/// Independent integer-enumeration reference for the eager-time semantics (engine_plan §0),
/// deliberately NOT using `must::time`. Returns whether the consistent terminal graph `g`
/// is time-realizable, or `None` if enumerating the delay vectors would exceed `budget`
/// (the caller then skips the time cross-check for this graph).
///
/// Integrality (engine_plan §5.в): fixing an integer delay `d(s) ∈ [lo, hi] ∩ ℤ` per send
/// turns every §0 constraint into a difference `x − y ≤ c` with integer `c`; the feasible
/// region is a difference-bound polytope, which is integral, so real feasibility ⇔ integer
/// feasibility. No horizon is needed because every window here is finite (Б3).
pub fn time_feasible_ref(g: &ExecutionGraph, budget: &mut usize) -> Option<bool> {
    let sends: Vec<EventId> = g.iter_sends().collect();
    let windows: Vec<(u64, u64)> = sends
        .iter()
        .map(|&s| {
            let w = g.send_window(s).expect("send has a window");
            (
                w.lo(),
                w.hi().expect("time_feasible_ref requires finite windows"),
            )
        })
        .collect();
    let combos: u128 = windows
        .iter()
        .map(|&(lo, hi)| (hi - lo + 1) as u128)
        .product();
    if combos > *budget as u128 {
        return None;
    }
    *budget -= combos as usize;

    let send_idx: BTreeMap<EventId, usize> =
        sends.iter().enumerate().map(|(i, &s)| (s, i)).collect();
    let n = sends.len();
    let spans: Vec<usize> = windows.iter().map(|&(lo, hi)| (hi - lo) as usize).collect();

    let mut off = vec![0usize; n];
    loop {
        let d: Vec<i64> = (0..n)
            .map(|i| windows[i].0 as i64 + off[i] as i64)
            .collect();
        let mut eval = TimeEval {
            g,
            send_idx: &send_idx,
            d: &d,
            fire: BTreeMap::new(),
        };
        if eval.feasible() {
            return Some(true);
        }
        // Advance the mixed-radix offset; a full wrap means no delay vector worked.
        if n == 0 {
            return Some(false);
        }
        let mut i = 0;
        loop {
            if i == n {
                return Some(false);
            }
            off[i] += 1;
            if off[i] <= spans[i] {
                break;
            }
            off[i] = 0;
            i += 1;
        }
    }
}

// -- Runtime (coroutine) oracle helpers -------------------------------------------

/// Run a coroutine `System` under a representative set of priority permutations of its
/// `n` threads and assert the two invariants that must hold for *any* correct Must run,
/// regardless of a hand-derived count:
///   * **no duplicates** -- distinct canonical `(E, po, rf)` keys over full-or-blocked
///     terminals;
///   * **priority invariance** -- the terminal-key set and the `(full, blocked)` counts
///     are identical across permutations (completeness + optimality).
///
/// Also asserts `error_count == 0` (the correct-protocol case; broken variants go through
/// [`assert_monitor_bites`] instead). Returns the invariant `(full, blocked)`.
///
/// All permutations for `n <= 4`; a representative sample ([`sample_perms`]) beyond that.
/// `make` builds a fresh system per run (the runtime is not shareable across threads).
pub fn assert_system_invariant(
    make: impl Fn() -> System + Sync,
    n: usize,
    name: &str,
) -> (usize, usize) {
    let perms = if n <= 4 {
        permutations(n)
    } else {
        sample_perms(n)
    };
    let mut reference: Option<BTreeSet<String>> = None;
    let mut counts = (0, 0);
    for perm in &perms {
        let col = ExecutionCollector::new();
        explore(&make, &col, Config::default().with_priorities(perm.clone()));
        assert_eq!(
            col.error_count(),
            0,
            "{name} under priorities {perm:?}: unexpected safety violation (error_count)"
        );
        let keys = col.terminal_keys();
        let set: BTreeSet<String> = keys.iter().cloned().collect();
        assert_eq!(
            keys.len(),
            set.len(),
            "{name}: duplicate terminal keys under priorities {perm:?}:\n{keys:#?}"
        );
        match &reference {
            None => {
                reference = Some(set);
                counts = (col.full_count(), col.blocked_count());
            }
            Some(r) => assert_eq!(
                &set, r,
                "{name}: terminal key set differs under priorities {perm:?} \
                 (executions must be priority-invariant)"
            ),
        }
    }
    counts
}

/// Whether some collected terminal execution has a receive reading no message -- the
/// witness that a crash (a `recv_timeout` timing out on a lost or slow message) is
/// genuinely exercised.
pub fn any_bottom_read(col: &ExecutionCollector) -> bool {
    col.terminals().iter().any(|e| {
        let g = e.graph();
        g.recvs().into_iter().any(|r| g.reads_bottom(r))
    })
}

/// Negative safety oracle: a deliberately broken protocol variant must make its monitor
/// bite. Runs with [`Config::collect_errors`] (so *every* violating execution surfaces as
/// its own `Error` terminal rather than aborting the whole search at the first one), under
/// a representative sweep of the `n`-thread priority permutations, and asserts on *each*:
///   * `error_count > 0` -- the monitor caught at least one violation;
///   * `blocked_count == 0`;
///   * `full_count + error_count == base` -- the broken variant has the *same* executions
///     as the correct one (`base`), only reclassified: a violation turns a would-be full
///     execution into an error terminal (a second, independent check on `base`);
///   * the `(full, error)` split and the full-or-blocked key-set are **priority-invariant**
///     (so the classification is schedule-independent, matching the positive oracles).
///
/// Returns the invariant `(full, error)` split so callers can assert the exact numbers.
/// `make` builds a fresh system per run (the runtime is not shareable across threads).
pub fn assert_monitor_bites(
    make: impl Fn() -> System + Sync,
    n: usize,
    base: usize,
    name: &str,
) -> (usize, usize) {
    let perms = if n <= 4 {
        permutations(n)
    } else {
        sample_perms(n)
    };
    let mut reference: Option<(BTreeSet<String>, usize, usize)> = None;
    for perm in &perms {
        let col = ExecutionCollector::new();
        explore(
            &make,
            &col,
            Config::default()
                .with_priorities(perm.clone())
                .collect_errors(),
        );
        assert!(
            col.error_count() > 0,
            "{name} under priorities {perm:?}: expected the monitor to catch a violation"
        );
        assert_eq!(
            col.blocked_count(),
            0,
            "{name} under priorities {perm:?}: unexpected blocked executions"
        );
        assert_eq!(
            col.full_count() + col.error_count(),
            base,
            "{name} under priorities {perm:?}: full ({}) + error ({}) != base {base}",
            col.full_count(),
            col.error_count()
        );
        let keys = col.terminal_keys();
        let set: BTreeSet<String> = keys.iter().cloned().collect();
        assert_eq!(
            keys.len(),
            set.len(),
            "{name} under priorities {perm:?}: duplicate terminal keys"
        );
        let split = (col.full_count(), col.error_count());
        match &reference {
            None => reference = Some((set, split.0, split.1)),
            Some((rset, rf, re)) => {
                assert_eq!(&set, rset, "{name}: terminal set differs under {perm:?}");
                assert_eq!(
                    split,
                    (*rf, *re),
                    "{name}: (full,error) differs under {perm:?}"
                );
            }
        }
    }
    let (_, full, error) = reference.expect("at least one permutation");
    (full, error)
}

// -- Two-phase commit (2PC) model -------------------------------------------------

/// Which (if any) safety bug a [`twopc_system`] coordinator has.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TwoPcBug {
    /// Correct: COMMIT iff every participant voted YES; a timed-out vote (no message) =>
    /// ABORT.
    None,
    /// Atomicity bug: commit regardless of the votes.
    IgnoreVotes,
    /// Atomicity bug: treat a timed-out vote (no message) as a YES (commit unless an
    /// *explicit* NO was seen).
    TimeoutMeansYes,
    /// Agreement bug: the global decision (and `DN`) is ABORT, but participant 1 is told to
    /// COMMIT -- so the participants adopt *different* decisions. Isolates the monitor's
    /// **agreement** assert: atomicity cannot fire (no global commit), so only the
    /// disagreement is caught.
    DivergentDecision,
}

/// Build a two-phase-commit `System`: coordinator `= tid 0`, participants `= 1..=n`, and
/// (when `monitored`) an atomicity/agreement monitor `Tm = tid n+1`. Protocol messages
/// use `model`; **all monitor notifications use `Model::Cd`**. When `crash`, the
/// coordinator collects votes with `recv_timeout`, so a lost or slow vote reads no message
/// (a suspected -- possibly false -- failure). Every participant always runs to
/// completion; a "crash" is only what the coordinator *observes*.
pub fn twopc_system(n: usize, model: Model, crash: bool, monitored: bool, bug: TwoPcBug) -> System {
    let mut sys = System::new();
    let tm = n + 1;

    // coordinator = tid 0
    sys.add(move |c| async move {
        for p in 1..=n {
            c.send(p, "PREP", model); // msg 1: PREPARE
        }
        let mut votes: Vec<Option<String>> = Vec::with_capacity(n);
        for p in 1..=n {
            let prefix = format!("V:{p}:");
            let v = if crash {
                c.recv_timeout(move |x: &str| x.starts_with(&prefix)).await
            } else {
                Some(c.recv(move |x: &str| x.starts_with(&prefix)).await)
            };
            votes.push(v); // msg 2: VOTE (None = suspected crash)
        }
        let decision = match bug {
            TwoPcBug::IgnoreVotes => "COMMIT",
            TwoPcBug::TimeoutMeansYes => {
                // A timeout (no message) treated as YES: abort only on an explicit NO.
                if votes
                    .iter()
                    .any(|v| v.as_deref().is_some_and(|s| s.ends_with("NO")))
                {
                    "ABORT"
                } else {
                    "COMMIT"
                }
            }
            // The global decision is ABORT; the per-participant divergence is applied at
            // broadcast time below.
            TwoPcBug::DivergentDecision => "ABORT",
            TwoPcBug::None => {
                // Correct: all-YES => COMMIT, else (incl. any timeout) => ABORT.
                if votes
                    .iter()
                    .all(|v| v.as_deref().is_some_and(|s| s.ends_with("YES")))
                {
                    "COMMIT"
                } else {
                    "ABORT"
                }
            }
        };
        if monitored {
            c.send(tm, format!("DN:{decision}"), Model::Cd); // msg 3n: BEFORE broadcast
        }
        for p in 1..=n {
            // DivergentDecision tells participant 1 to COMMIT while the global (DN) is
            // ABORT -- the participants adopt different decisions (agreement violation).
            let d_p = if bug == TwoPcBug::DivergentDecision && p == 1 {
                "COMMIT"
            } else {
                decision
            };
            c.send(p, format!("D:{d_p}"), model); // msg 3: DECISION
        }
    });

    // participants = tids 1..=n
    for p in 1..=n {
        sys.add(move |c| async move {
            let _ = c.recv(|x: &str| x == "PREP").await; // msg 1
            let vote = c.nondet(["NO", "YES"]).await; // ND^S: min(S)="NO" first
            if monitored {
                c.send(tm, format!("VN:{p}:{vote}"), Model::Cd); // msg 2n: BEFORE the vote send
            }
            c.send(0, format!("V:{p}:{vote}"), model); // msg 2
            let d = c.recv(|x: &str| x.starts_with("D:")).await; // msg 3
            if monitored {
                let dec = d.strip_prefix("D:").unwrap_or(&d).to_string();
                c.send(tm, format!("AN:{p}:{dec}"), Model::Cd); // msg 4n: AFTER the decision recv
            }
        });
    }

    // monitor = tid n+1
    if monitored {
        sys.add(move |c| async move {
            let mut vn: Vec<String> = Vec::with_capacity(n);
            for p in 1..=n {
                let prefix = format!("VN:{p}:");
                vn.push(c.recv(move |x: &str| x.starts_with(&prefix)).await);
            }
            let dn = c.recv(|x: &str| x.starts_with("DN:")).await;
            let mut an: Vec<String> = Vec::with_capacity(n);
            for p in 1..=n {
                let prefix = format!("AN:{p}:");
                an.push(c.recv(move |x: &str| x.starts_with(&prefix)).await);
            }
            let commit = dn == "DN:COMMIT";
            // Atomicity/validity: a global COMMIT requires every true vote to be YES.
            let all_yes = vn.iter().all(|v| v.ends_with("YES"));
            c.assert_that(!commit || all_yes, "atomicity: COMMIT requires all YES");
            // Agreement: every participant adopted the single global decision.
            let global = dn.strip_prefix("DN:").unwrap_or(&dn);
            for a in &an {
                let dec = a.rsplit(':').next().unwrap_or("");
                c.assert_that(
                    dec == global,
                    "agreement: participant adopted the global decision",
                );
            }
        });
    }

    sys
}

// -- Leader election model --------------------------------------------------------

/// Which (if any) tie-break bug a [`leader_system`] node has.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LeaderBug {
    /// Correct: ties broken by lowest tid (a deterministic function of the ballot view).
    None,
    /// Bug: a node breaks ties in its *own* favour, so two tied nodes disagree.
    SelfishTieBreak,
}

/// The elected leader given a node's `view` of `(ballot, tid)` (highest ballot wins).
/// Correct tie-break is lowest tid; [`LeaderBug::SelfishTieBreak`] prefers `me` when `me`
/// is tied for the maximum.
fn leader_winner(view: &[Option<(u32, usize)>], me: usize, bug: LeaderBug) -> usize {
    let max_b = view.iter().flatten().map(|&(b, _)| b).max().unwrap_or(0);
    let tied: Vec<usize> = view
        .iter()
        .flatten()
        .filter(|&&(b, _)| b == max_b)
        .map(|&(_, tid)| tid)
        .collect();
    match bug {
        LeaderBug::None => *tied.iter().min().unwrap(),
        LeaderBug::SelfishTieBreak => {
            if tied.contains(&me) {
                me
            } else {
                *tied.iter().min().unwrap()
            }
        }
    }
}

/// Build a leader-election `System`: `n` nodes `0..n`, and (when `monitored`) a uniqueness
/// monitor `Tm = tid n`. Each node's ballot is the sum of `incr` nondet increments from
/// `{1,2,3}` (`leader(n, incr)`); it broadcasts its ballot to every peer, collects theirs
/// (with `recv_timeout` when `crash`, so a lost ballot reads no message => no quorum), and
/// elects the highest ballot (ties by lowest tid, unless `bug`). Monitored nodes
/// **always** announce their elected leader under `Model::Cd` -- even without a quorum
/// (the *naive* protocol), which is what exposes split-brain under crashes.
pub fn leader_system(
    n: usize,
    incr: usize,
    model: Model,
    crash: bool,
    monitored: bool,
    bug: LeaderBug,
) -> System {
    let mut sys = System::new();
    let tm = n;

    for k in 0..n {
        sys.add(move |c| async move {
            let mut ballot: u32 = 0;
            for _ in 0..incr {
                let v = c.nondet(["1", "2", "3"]).await;
                ballot += v.parse::<u32>().unwrap_or(0);
            }
            for j in 0..n {
                if j != k {
                    c.send(j, format!("B:{k}:{ballot}"), model); // broadcast ballot
                }
            }
            let mut view: Vec<Option<(u32, usize)>> = vec![None; n];
            // `j` is the peer's tid: it names both the selective predicate `"B:{j}:"` and
            // the `view` slot, so a bare iterator would lose the intent.
            #[allow(clippy::needless_range_loop)]
            for j in 0..n {
                if j == k {
                    view[k] = Some((ballot, k));
                    continue;
                }
                let prefix = format!("B:{j}:");
                let r = if crash {
                    c.recv_timeout(move |x: &str| x.starts_with(&prefix)).await
                } else {
                    Some(c.recv(move |x: &str| x.starts_with(&prefix)).await)
                };
                // r == None: peer j's ballot timed out -- no quorum, but the naive
                // protocol still announces below.
                let b = match r {
                    Some(msg) => msg
                        .rsplit(':')
                        .next()
                        .and_then(|s| s.parse::<u32>().ok())
                        .unwrap_or(0),
                    None => continue,
                };
                view[j] = Some((b, j));
            }
            let winner = leader_winner(&view, k, bug);
            if monitored {
                c.send(tm, format!("A:{k}:{winner}"), Model::Cd);
            }
        });
    }

    if monitored {
        sys.add(move |c| async move {
            let mut ann: Vec<String> = Vec::with_capacity(n);
            for k in 0..n {
                let prefix = format!("A:{k}:");
                ann.push(c.recv(move |x: &str| x.starts_with(&prefix)).await);
            }
            let w0 = ann[0].rsplit(':').next().unwrap_or("").to_string();
            for a in &ann[1..] {
                let w = a.rsplit(':').next().unwrap_or("");
                c.assert_that(w == w0, "uniqueness: nodes disagree on the leader");
            }
        });
    }

    sys
}

// -- Brute-force reference for the existential viable(v) oracle (T2_ORACLE_SPEC §1.8 O2) ----

/// Every consistent state forward-reachable from `h0`: from each state, each thread's next
/// event is resolved every legal way (send/error added; nondet at every value; a receive at
/// every present send and ⊥ — reading the revisiting send included). BFS over contents,
/// deduped by canonical key. No feasibility pruning, no drain ordering, no memo — fully
/// independent of the `viable` search structure.
pub fn all_states<P: Program>(h0: &ExecutionGraph, program: &P) -> Vec<ExecutionGraph> {
    let n = program.num_threads();
    let mut seen: BTreeMap<String, ExecutionGraph> = BTreeMap::new();
    let mut queue: std::collections::VecDeque<ExecutionGraph> = std::collections::VecDeque::new();
    if must::consistent(h0) {
        seen.insert(h0.canonical_key(), h0.clone());
        queue.push_back(h0.clone());
    }
    while let Some(h) = queue.pop_front() {
        let traces = must::traces_of(&h, n);
        let nexts = program.next(&traces);
        for (tid, next) in nexts.iter().enumerate() {
            let ThreadNext::Next(label) = next else {
                continue;
            };
            let mut children: Vec<ExecutionGraph> = Vec::new();
            match label {
                Label::Send { .. } | Label::Error { .. } => {
                    let mut c = h.clone();
                    c.add_event(tid, label.clone());
                    children.push(c);
                }
                Label::Nondet { set } => {
                    for &v in set.iter() {
                        let mut c = h.clone();
                        let e = c.add_event(tid, label.clone());
                        c.set_nd(e, v);
                        children.push(c);
                    }
                }
                Label::Recv { .. } => {
                    let mut c = h.clone();
                    let e = c.add_event(tid, label.clone());
                    c.set_rf(e, None);
                    let mut opts: Vec<Option<EventId>> = c.iter_sends().map(Some).collect();
                    opts.push(None);
                    for src in opts {
                        let mut c2 = c.clone();
                        c2.set_rf(e, src);
                        children.push(c2);
                    }
                }
            }
            for c in children {
                if !must::consistent(&c) {
                    continue;
                }
                if let std::collections::btree_map::Entry::Vacant(slot) =
                    seen.entry(c.canonical_key())
                {
                    slot.insert(c.clone());
                    queue.push_back(c);
                }
            }
        }
    }
    seen.into_values().collect()
}

/// Reference verdict for `must::time::viable` (§1.4 success over ALL reachable states):
/// ∃ a state where `revisiting` is present-unread with `rev_label` and the state passes
/// feasibility plus the visitability gate.
#[allow(clippy::too_many_arguments)]
pub fn brute_viable<P: Program>(
    base: &ExecutionGraph,
    ep: EventId,
    v: Val,
    program: &P,
    priorities: &[usize],
    revisiting: EventId,
    rev_label: &Label,
) -> bool {
    let mut h0 = base.clone();
    h0.set_nd(ep, v);
    all_states(&h0, program).iter().any(|h| {
        h.contains(revisiting)
            && h.label(revisiting) == rev_label
            && !h.is_read(revisiting)
            && must::time::check(h).is_feasible()
            && must::time::gate_feasible(h, program, priorities)
    })
}
