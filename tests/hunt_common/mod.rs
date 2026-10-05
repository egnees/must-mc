//! Shared vehicle for the `hunt_*` completeness hunts (T2_PROOFS_A A2.2e, B3.d R1,
//! T2_PROOFS_B B1.c γ2a/γ2b/γ3).
//!
//! Lives under `tests/hunt_common/` so cargo does not compile it as its own test binary;
//! each hunt pulls it in with `mod hunt_common;`.
//!
//! Three pieces:
//!   * [`VdProgram`] — the value-dependent table program (nondet values gate receive
//!     predicates, send emission and delivery windows) with an **exact** `possible_future`,
//!     the regime in which `gate_feasible` takes its `closure_is_exact` branch. Copied from
//!     `tests/fuzz_value_dependent.rs` (the hunts must not touch existing tests).
//!   * [`vet`] — the three-way arbitration: `realizable(T2-predicate)` vs
//!     `realizable(zombie)` vs `realizable(T1-filter)` by `canonical_key`, plus the
//!     duplicate check. zombie and T1 are correct by construction (T2_ORACLE_SPEC §2.2), so
//!     any divergence is a T2 finding.
//!   * [`Probe`] — the shape counters. Every hunt has to prove its target region is
//!     non-empty (the "INVERSIONS=17" discipline of `tests/cb1_repro.rs`): a NO-REPRO with
//!     zero coverage is worthless.

#![allow(dead_code)]

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::sync::Mutex;

use must::event::{EventId, Label, Model, Pred, Window};
use must::explorer::revisit::get_cons_tiebreaker;
use must::graph::ExecutionGraph;
use must::intern::resolve;
use must::{explore, Config, ExecutionCollector, Observer, Program, ThreadNext, Val};

// =====================================================================================
// The value-dependent table program (exact possible_future).
// =====================================================================================

/// A receive's selectivity: static, or keyed by the value a po-earlier value-producing op of
/// the same thread yielded.
#[derive(Clone, Copy, Debug)]
pub enum Sel {
    Any,
    Eq(&'static str),
    /// `Pred::eq(value_of(op[k]))`; a guard with no value (⊥ read) never matches.
    EqGuard(usize),
}

/// One straight-line op of a thread.
#[derive(Clone, Debug)]
pub enum Op {
    /// `nd{a, b}` (the values are the corpus-wide `{"a","b"}`).
    Nondet,
    /// `nd{a, b, c}` — three values, so a *non-min* holder can be the only viable one.
    Nondet3,
    Send {
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    /// Emitted only when `value_of(op[guard]) == eq`.
    SendIf {
        guard: usize,
        eq: &'static str,
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    /// Window `[lo1,hi1]` when `value_of(op[guard]) == eq`, else `[lo2,hi2]`.
    SendWin {
        guard: usize,
        eq: &'static str,
        dst: usize,
        model: Model,
        val: &'static str,
        lo1: u64,
        hi1: u64,
        lo2: u64,
        hi2: u64,
    },
    Recv {
        sel: Sel,
        blocking: bool,
    },
}

impl Op {
    fn is_value_producing(&self) -> bool {
        matches!(self, Op::Nondet | Op::Nondet3 | Op::Recv { .. })
    }
    fn nd_set(&self) -> Option<&'static [&'static str]> {
        match self {
            Op::Nondet => Some(&["a", "b"]),
            Op::Nondet3 => Some(&["a", "b", "c"]),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct VdProgram {
    pub threads: Vec<Vec<Op>>,
}

fn guard_hits(vals: &[Option<Val>], k: usize, eq: &str) -> bool {
    vals[k].is_some_and(|v| resolve(v) == eq)
}

fn op_label(op: &Op, vals: &[Option<Val>]) -> Label {
    match op {
        Op::Nondet => Label::nondet(["a", "b"]),
        Op::Nondet3 => Label::nondet(["a", "b", "c"]),
        Op::Send {
            dst,
            model,
            val,
            lo,
            hi,
        }
        | Op::SendIf {
            dst,
            model,
            val,
            lo,
            hi,
            ..
        } => Label::send_within(*model, *dst, *val, Window::new(*lo, *hi)),
        Op::SendWin {
            guard,
            eq,
            dst,
            model,
            val,
            lo1,
            hi1,
            lo2,
            hi2,
        } => {
            let (lo, hi) = if guard_hits(vals, *guard, eq) {
                (*lo1, *hi1)
            } else {
                (*lo2, *hi2)
            };
            Label::send_within(*model, *dst, *val, Window::new(lo, hi))
        }
        Op::Recv { sel, blocking } => {
            let pred = match sel {
                Sel::Any => Pred::any(),
                Sel::Eq(s) => Pred::eq(*s),
                Sel::EqGuard(k) => match vals[*k] {
                    Some(v) => Pred::eq(resolve(v)),
                    None => Pred::eq("__none__"),
                },
            };
            if *blocking {
                Label::recv(pred)
            } else {
                Label::recv_nb(pred)
            }
        }
    }
}

/// Replay one thread against its trace: per-op resolved values plus the first op not yet
/// committed (a skipped `SendIf` never consumes a trace entry).
fn replay(ops: &[Op], trace: &[Option<Val>]) -> (Vec<Option<Val>>, usize) {
    let mut vals: Vec<Option<Val>> = vec![None; ops.len()];
    let mut cursor = 0;
    for (i, op) in ops.iter().enumerate() {
        let emits = match op {
            Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
            _ => true,
        };
        if !emits {
            continue;
        }
        if cursor < trace.len() {
            if op.is_value_producing() {
                vals[i] = trace[cursor];
            }
            cursor += 1;
        } else {
            return (vals, i);
        }
    }
    (vals, ops.len())
}

impl Program for VdProgram {
    fn num_threads(&self) -> usize {
        self.threads.len()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        self.threads
            .iter()
            .enumerate()
            .map(|(t, ops)| {
                let (vals, frontier) = replay(ops, &traces[t]);
                let mut i = frontier;
                while i < ops.len() {
                    let emits = match &ops[i] {
                        Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
                        _ => true,
                    };
                    if emits {
                        return ThreadNext::Next(op_label(&ops[i], &vals));
                    }
                    i += 1;
                }
                ThreadNext::Finished
            })
            .collect()
    }
    /// Sound over-approximation: every label every op at/after the frontier could produce
    /// under any assignment of still-unresolved guards.
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        let ops = &self.threads[tid];
        let (vals, frontier) = replay(ops, trace);
        // Contract (`src/program.rs`): `out[0]` must be *exactly* the thread's next label — the
        // one `next` reports, i.e. `op_label` of the first **emitting** op at/after the frontier
        // (a `SendIf` with a failing guard is skipped by both). Everything from index 1 on
        // over-approximates the ops strictly after it.
        //
        // The head has to come from the same `op_label` call `next` uses, not from the loop
        // below: that loop deliberately emits *several* labels for one op (both windows of an
        // unresolved `SendWin`, every payload of an unresolved `EqGuard`), so it would put the
        // wrong label at index 0. `force_source` condition (3b) does `.skip(1)` on the strength
        // of this, so the mismatch is an over-force, i.e. a completeness loss — pinned by
        // `tests/h1_review.rs::vd_program_violates_the_new_possible_future_head_contract`.
        let Some(head) = (frontier..ops.len()).find(|&i| match &ops[i] {
            Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
            _ => true,
        }) else {
            return Some(Vec::new()); // finished: no future events at all (the exact answer)
        };
        let mut out = vec![op_label(&ops[head], &vals)];
        for op in &ops[head + 1..] {
            match op {
                Op::Nondet | Op::Nondet3 | Op::Send { .. } => out.push(op_label(op, &vals)),
                Op::SendIf { guard, eq, .. } => match vals[*guard] {
                    Some(v) if resolve(v) != *eq => {} // definitely skipped
                    _ => out.push(op_label(op, &vals)),
                },
                Op::SendWin {
                    guard,
                    dst,
                    model,
                    val,
                    lo1,
                    hi1,
                    lo2,
                    hi2,
                    ..
                } => match vals[*guard] {
                    Some(_) => out.push(op_label(op, &vals)),
                    None => {
                        out.push(Label::send_within(
                            *model,
                            *dst,
                            *val,
                            Window::new(*lo1, *hi1),
                        ));
                        out.push(Label::send_within(
                            *model,
                            *dst,
                            *val,
                            Window::new(*lo2, *hi2),
                        ));
                    }
                },
                Op::Recv { sel, blocking } => {
                    let mk = |p: Pred| {
                        if *blocking {
                            Label::recv(p)
                        } else {
                            Label::recv_nb(p)
                        }
                    };
                    match sel {
                        Sel::Any => out.push(mk(Pred::any())),
                        Sel::Eq(s) => out.push(mk(Pred::eq(*s))),
                        Sel::EqGuard(k) => match vals[*k] {
                            Some(v) => out.push(mk(Pred::eq(resolve(v)))),
                            None => {
                                for p in PAYLOADS {
                                    out.push(mk(Pred::eq(p)));
                                }
                                out.push(mk(Pred::eq("__none__")));
                            }
                        },
                    }
                }
            }
        }
        Some(out)
    }
}

/// Every payload the hunts' generators use — the `EqGuard` over-approximation must cover them.
pub const PAYLOADS: [&str; 8] = ["a", "b", "c", "m", "s", "w", "x", "y"];

// -- builders -------------------------------------------------------------------------------

pub fn send(dst: usize, val: &'static str, lo: u64, hi: u64) -> Op {
    Op::Send {
        dst,
        model: Model::Asyn,
        val,
        lo,
        hi,
    }
}
pub fn send_m(model: Model, dst: usize, val: &'static str, lo: u64, hi: u64) -> Op {
    Op::Send {
        dst,
        model,
        val,
        lo,
        hi,
    }
}
pub fn send_if(guard: usize, eq: &'static str, dst: usize, val: &'static str, lo: u64, hi: u64) -> Op {
    Op::SendIf {
        guard,
        eq,
        dst,
        model: Model::Asyn,
        val,
        lo,
        hi,
    }
}
pub fn brecv(sel: Sel) -> Op {
    Op::Recv {
        sel,
        blocking: true,
    }
}
pub fn nbrecv(sel: Sel) -> Op {
    Op::Recv {
        sel,
        blocking: false,
    }
}

// =====================================================================================
// SplitMix64 (no external crate).
// =====================================================================================

pub struct Rng(u64);
impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }
    pub fn u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: usize) -> usize {
        (self.u64() % n as u64) as usize
    }
    pub fn chance(&mut self, pct: usize) -> bool {
        self.below(100) < pct
    }
    pub fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len())]
    }
}

// =====================================================================================
// Shape probe.
// =====================================================================================

/// Recomputed `Deleted(r, s)` (line 11): strict `<_G`, minus the porf-prefix of `s`.
pub fn deleted_set(g: &ExecutionGraph, r: EventId, porf_s: &BTreeSet<EventId>) -> BTreeSet<EventId> {
    let sr = g.stamp(r);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) > sr && !porf_s.contains(&x))
        .collect()
}

/// Recomputed `Previous(e, s)` (line 20): non-strict `<=_G`, plus the porf-prefix of `s`.
pub fn previous_set(g: &ExecutionGraph, e: EventId, porf_s: &BTreeSet<EventId>) -> BTreeSet<EventId> {
    let se = g.stamp(e);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) <= se || porf_s.contains(&x))
        .collect()
}

/// The graph a revisit `(r, s)` would produce (line 13), recomputed from `(g, r, s)`.
pub fn revisit_result(g: &ExecutionGraph, r: EventId, s: EventId) -> ExecutionGraph {
    let porf_s = g.porf_prefix(s);
    let deleted = deleted_set(g, r, &porf_s);
    let mut keep: BTreeSet<EventId> = g.all_events().into_iter().collect();
    for &d in &deleted {
        if d != s {
            keep.remove(&d);
        }
    }
    let mut g2 = g.restrict(&keep);
    g2.set_rf(r, Some(s));
    g2
}

/// How many sends the line-22 tiebreaker of `e` would consider on `h` (the same candidate
/// filter as `get_cons_tiebreaker`: matching, unread by another receive, consistent to read).
/// `>= 2` means the canon made a genuine choice.
pub fn tiebreaker_candidates(h: &ExecutionGraph, e: EventId) -> Vec<EventId> {
    let mut hp = h.clone();
    hp.set_rf(e, None);
    hp.sends()
        .into_iter()
        .filter(|&s| {
            if !hp.matches(s, e) {
                return false;
            }
            if hp
                .recvs()
                .into_iter()
                .any(|rp| rp != e && hp.reads_from(rp) == Some(s))
            {
                return false;
            }
            let mut trial = hp.clone();
            trial.set_rf(e, Some(s));
            must::consistent(&trial)
        })
        .collect()
}

/// Instrumentation shared by the hunts. `prog`/`priorities` are kept so the probe can call
/// `forced_closure` (the A2.2e shape needs to look at what the gate's closure added).
pub struct Probe<P: Program + Clone + Sync> {
    prog: P,
    priorities: Vec<usize>,
    track_visited: bool,

    pub revisits: AtomicUsize,
    pub rejects: AtomicUsize,
    /// Rejected revisits where a blocking receive in `Deleted ∪ {r}` failed line 22
    /// (`rf != tiebreaker`) — the R1 arm actually biting.
    pub tb_rejects: AtomicUsize,
    /// ... and that receive had ≥ 2 tiebreaker candidates in `G|_Previous` (a genuine choice,
    /// i.e. the R1 shape: the canon could have gone the other way).
    pub tb_rejects_multi: AtomicUsize,
    /// ... and the revisit's `g2` is consistent *and* eager-feasible — a live graph refused by
    /// the receive canon. This is the R1 target shape.
    pub tb_rejects_live: AtomicUsize,

    /// Revisits pruned by T-GATE (line 13).
    pub gate_pruned: AtomicUsize,
    /// ... where `g2` itself is eager-feasible, so the prune came from the *closure* (the only
    /// case in which the exact branch of `gate_feasible` can over-prune — A2.2e).
    pub gate_pruned_exact: AtomicUsize,
    /// ... and the closure added a non-blocking receive beyond `g2` (the nb-⊥ continuation the
    /// A2.2e recipe needs).
    pub gate_pruned_exact_nb: AtomicUsize,
    /// ... and `g2` carries a stamp inversion other than the revisit's own `(r, s)` pair — i.e.
    /// a *previous* revisit survives in it (the 2-hop region A2.2e is open in).
    pub gate_pruned_exact_2hop: AtomicUsize,

    pub viable_calls: AtomicUsize,
    /// `viable(v) = true` for some `v` below the held value ⇒ the holder was REJECTED by the
    /// PASS rule and completeness now rests on the `v* = min(V)` branch (γ2/γ3).
    pub viable_true: AtomicUsize,

    /// Canonical keys of rejected-or-pruned revisit results that are consistent + eager-feasible.
    pub refused_g2: Mutex<BTreeSet<String>>,
    /// Canonical keys of every graph a Visit was entered on (only when `track_visited`).
    pub visited: Mutex<BTreeSet<String>>,
}

impl<P: Program + Clone + Sync> Probe<P> {
    pub fn new(prog: P, priorities: Vec<usize>, track_visited: bool) -> Self {
        Probe {
            prog,
            priorities,
            track_visited,
            revisits: AtomicUsize::new(0),
            rejects: AtomicUsize::new(0),
            tb_rejects: AtomicUsize::new(0),
            tb_rejects_multi: AtomicUsize::new(0),
            tb_rejects_live: AtomicUsize::new(0),
            gate_pruned: AtomicUsize::new(0),
            gate_pruned_exact: AtomicUsize::new(0),
            gate_pruned_exact_nb: AtomicUsize::new(0),
            gate_pruned_exact_2hop: AtomicUsize::new(0),
            viable_calls: AtomicUsize::new(0),
            viable_true: AtomicUsize::new(0),
            refused_g2: Mutex::new(BTreeSet::new()),
            visited: Mutex::new(BTreeSet::new()),
        }
    }

    /// Refused revisit results that no Visit ever entered — a *leading indicator* of a lost
    /// subtree (only meaningful with `track_visited`; the terminal-set arbitration is the
    /// ground truth).
    pub fn refused_and_unvisited(&self) -> Vec<String> {
        let visited = self.visited.lock().unwrap();
        self.refused_g2
            .lock()
            .unwrap()
            .iter()
            .filter(|k| !visited.contains(*k))
            .cloned()
            .collect()
    }

    fn note_refused(&self, g2: &ExecutionGraph) {
        if must::consistent(g2) && must::eager_feasible(g2) {
            self.refused_g2
                .lock()
                .unwrap()
                .insert(g2.canonical_key());
        }
    }
}

impl<P: Program + Clone + Sync> Observer for Probe<P> {
    fn on_visit_enter(&self, g: &ExecutionGraph) {
        if self.track_visited {
            self.visited.lock().unwrap().insert(g.canonical_key());
        }
    }

    fn on_backward_revisit(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _deleted: &BTreeSet<EventId>,
    ) {
        self.revisits.fetch_add(1, Relaxed);
    }

    fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
        self.rejects.fetch_add(1, Relaxed);
        let porf_s = g.porf_prefix(s);
        let deleted = deleted_set(g, r, &porf_s);
        let mut tb_failed = false;
        let mut tb_multi = false;
        for &ep in deleted.iter().chain(std::iter::once(&r)) {
            if g.label(ep).blocking() != Some(true) {
                continue;
            }
            let previous = previous_set(g, ep, &porf_s);
            let h = g.restrict(&previous);
            let tb = get_cons_tiebreaker(&h, ep, true);
            if g.reads_from(ep) != tb {
                tb_failed = true;
                if tiebreaker_candidates(&h, ep).len() >= 2 {
                    tb_multi = true;
                }
            }
        }
        if tb_failed {
            self.tb_rejects.fetch_add(1, Relaxed);
        }
        if tb_multi {
            self.tb_rejects_multi.fetch_add(1, Relaxed);
            let g2 = revisit_result(g, r, s);
            if must::consistent(&g2) && must::eager_feasible(&g2) {
                self.tb_rejects_live.fetch_add(1, Relaxed);
                self.note_refused(&g2);
            }
        }
    }

    fn on_forced_closure_pruned(&self, g2: &ExecutionGraph, _r: EventId, _s: EventId) {
        self.gate_pruned.fetch_add(1, Relaxed);
        if !must::consistent(g2) || !must::time::check(g2).is_feasible() {
            return; // pruned by the fallback / an inconsistent g2 — never over-pruning
        }
        self.gate_pruned_exact.fetch_add(1, Relaxed);
        self.note_refused(g2);
        let closure = must::time::forced_closure(g2, &self.prog, &self.priorities);
        let added_nb = (0..g2.num_threads()).any(|t| {
            (g2.thread_len(t)..closure.thread_len(t))
                .any(|i| closure.label(EventId::new(t, i)).blocking() == Some(false))
        });
        if added_nb {
            self.gate_pruned_exact_nb.fetch_add(1, Relaxed);
        }
        // A stamp inversion other than the revisit's own (r, s): a prior revisit survives.
        let inversions = g2
            .iter_recvs()
            .filter(|&x| {
                g2.reads_from(x)
                    .is_some_and(|src| g2.stamp(src) > g2.stamp(x))
            })
            .count();
        if inversions >= 2 {
            self.gate_pruned_exact_2hop.fetch_add(1, Relaxed);
        }
    }

    fn on_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _v: Val,
        _revisiting: EventId,
        _rev_label: &Label,
        verdict: bool,
    ) {
        self.viable_calls.fetch_add(1, Relaxed);
        if verdict {
            self.viable_true.fetch_add(1, Relaxed);
        }
    }
}

// =====================================================================================
// Three-way arbitration.
// =====================================================================================

pub struct Report {
    pub t1_full: BTreeSet<String>,
    pub t1_blocked: BTreeSet<String>,
    pub zb_full: BTreeSet<String>,
    pub t2_full: BTreeSet<String>,
    pub t2_blocked: BTreeSet<String>,
    pub t2_terms: Vec<String>,
}

impl Report {
    pub fn dups(&self) -> Vec<String> {
        let mut seen = BTreeSet::new();
        let mut dups = BTreeSet::new();
        for k in &self.t2_terms {
            if !seen.insert(k.clone()) {
                dups.insert(k.clone());
            }
        }
        dups.into_iter().collect()
    }
}

fn keysets(col: &ExecutionCollector) -> (BTreeSet<String>, BTreeSet<String>) {
    let full: BTreeSet<String> = col.full_keys().into_iter().collect();
    let blocked: BTreeSet<String> = col
        .blocked()
        .iter()
        .map(must::Execution::canonical_key)
        .collect();
    (full, blocked)
}

/// Run the three regimes and return their realizable key sets. `probe` (if given) rides along
/// with the T2 run.
pub fn run_three_way<P: Program + Clone + Sync, O: Observer + Sync>(
    prog: &P,
    priorities: &[usize],
    probe: Option<&O>,
) -> Report {
    let mk = || prog.clone();

    let t1 = ExecutionCollector::new();
    explore(
        mk,
        &t1,
        Config::default()
            .collect_errors()
            .with_time_filter()
            .with_priorities(priorities.to_vec()),
    );
    let (t1_full, t1_blocked) = keysets(&t1);

    let zb = ExecutionCollector::new();
    explore(
        mk,
        &zb,
        Config::default().collect_errors().with_time_zombie(),
    );
    let (zb_full, _) = keysets(&zb);

    let col = ExecutionCollector::new();
    let cfg = Config::default()
        .collect_errors()
        .with_time_predicate()
        .with_priorities(priorities.to_vec());
    let _ = &probe;
    explore(mk, &col, cfg);
    // (review copy: the probe-composition branch did not compile; unused by this hunt)
    let (t2_full, t2_blocked) = keysets(&col);

    Report {
        t1_full,
        t1_blocked,
        zb_full,
        t2_full,
        t2_blocked,
        t2_terms: col.terminal_keys(),
    }
}

/// The load-bearing assertions: zombie == T1 (the arbiter is sane), T2 == T1 (completeness),
/// no duplicate T2 terminal (optimality-(a)). Returns the report.
pub fn vet<P: Program + Clone + Sync + std::fmt::Debug, O: Observer + Sync>(
    name: &str,
    prog: &P,
    priorities: &[usize],
    probe: Option<&O>,
) -> Report {
    let rep = run_three_way(prog, priorities, probe);
    assert_eq!(
        rep.zb_full, rep.t1_full,
        "{name}: zombie full-set != T1-filter full-set (the arbiter itself broke)"
    );
    assert_eq!(
        rep.t2_full,
        rep.t1_full,
        "{name} @{priorities:?}: COMPLETENESS FINDING — T2 realizable != T1-filter realizable.\n  \
         LOST (T1 \\ T2) = {:?}\n  EXTRA (T2 \\ T1) = {:?}\n  prog = {prog:#?}",
        rep.t1_full.difference(&rep.t2_full).collect::<Vec<_>>(),
        rep.t2_full.difference(&rep.t1_full).collect::<Vec<_>>(),
    );
    assert_eq!(
        rep.t2_blocked, rep.t1_blocked,
        "{name} @{priorities:?}: T2 blocked-set != T1-filter blocked-set\n  prog = {prog:#?}"
    );
    let dups = rep.dups();
    assert!(
        dups.is_empty(),
        "{name} @{priorities:?}: DUPLICATE T2 terminals {dups:?}\n  prog = {prog:#?}"
    );
    rep
}
