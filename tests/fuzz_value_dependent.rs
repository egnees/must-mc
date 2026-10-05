//! T-DIFF: three-way differential fuzz on a **value-dependent** corpus
//! (T2_ORACLE_SPEC §3.2) — the blind spot the `SeqProgram` corpus structurally cannot cover
//! (value-independent programs make the min-feasible canon a no-op, T2_PLAN).
//!
//! The generator produces programs where nondet values influence (а) the predicates of
//! selective receives (`Sel::EqGuard`), (б) whether a send is emitted at all (`Op::SendIf` —
//! the raft LEADER shape), and (в) the delivery window (`Op::SendWin`); windows come from
//! near-tie bands (overlapping within 1–2 ticks) plus a late band, and the last thread is
//! biased into the consumed-competitor shape (§3.3 ingredient 2: two sequential receives
//! draining racing sends, with a value-gated downstream send).
//!
//! Per program:
//!   1. T1-filter across every priority permutation — the proven reference partition
//!      (asserted priority-invariant);
//!   2. zombie == T1 exactly (realizable and filtered key sets);
//!   3. T2-oracle (two permutations): realizable == T1 realizable, no duplicate keys,
//!      dead-branch count recorded (not asserted 0: the closure may be inexact on a
//!      value-dependent future);
//!   4. O2: every `viable` verdict the run made (via `Observer::on_viable_verdict`) is
//!      cross-checked against the brute-force enumeration of all completions.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use common::{brute_viable, permutations};
use must::event::{EventId, Label, Model, Pred, Window};
use must::graph::ExecutionGraph;
use must::intern::resolve;
use must::{
    explore, Config, CountingObserver, DeadBranchDetector, ExecutionCollector, Observer,
    Program, ThreadNext, Val,
};

/// SplitMix64 (copy of `fuzz.rs`) — reproducible with no external crate.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
    fn chance(&mut self, pct: usize) -> bool {
        self.below(100) < pct
    }
}

// -- The value-dependent program table ------------------------------------------------------

/// A receive's selectivity: static, or keyed by the value an earlier op of the SAME thread
/// produced (a nondet choice or a receive's read — the (а) axis).
#[derive(Clone, Copy, Debug)]
enum Sel {
    Any,
    Eq(&'static str),
    /// `Pred::eq(value_of(op[k]))`; a guard with no value (⊥ read) yields a never-matching
    /// predicate.
    EqGuard(usize),
}

/// One straight-line op of a thread. Guards always reference a po-earlier, value-producing
/// op (Nondet / Recv) of the same thread.
#[derive(Clone, Debug)]
enum Op {
    /// `nd{a, b}`.
    Nondet,
    Send {
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    /// Emitted only when `value_of(op[guard]) == eq` — the (б) emit/no-emit axis.
    SendIf {
        guard: usize,
        eq: &'static str,
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    /// Window `[lo1,hi1]` when `value_of(op[guard]) == eq`, else `[lo2,hi2]` — the (в) axis.
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
        matches!(self, Op::Nondet | Op::Recv { .. })
    }
}

/// The interpretable program: `threads[t]` is thread `t`'s op list.
#[derive(Clone, Debug)]
struct VdProgram {
    threads: Vec<Vec<Op>>,
}

/// Value of guard op `k` given the resolved `vals`, when it equals `eq`.
fn guard_hits(vals: &[Option<Val>], k: usize, eq: &str) -> bool {
    vals[k].is_some_and(|v| resolve(v) == eq)
}

/// The label op `op` produces given the thread's resolved `vals` so far.
fn op_label(op: &Op, vals: &[Option<Val>]) -> Label {
    match op {
        Op::Nondet => Label::nondet(["a", "b"]),
        Op::Send {
            dst,
            model,
            val,
            lo,
            hi,
        } => Label::send_within(*model, *dst, *val, Window::new(*lo, *hi)),
        Op::SendIf {
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
                    None => Pred::eq("__none__"), // never matches the {a,b} payloads
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

/// Replay one thread against its trace: resolved per-op values, plus the index of the first
/// op not yet committed (skipped `SendIf`s never consume a trace entry).
fn replay(ops: &[Op], trace: &[Option<Val>]) -> (Vec<Option<Val>>, usize) {
    let mut vals: Vec<Option<Val>> = vec![None; ops.len()];
    let mut cursor = 0;
    for (i, op) in ops.iter().enumerate() {
        let emits = match op {
            Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
            _ => true,
        };
        if !emits {
            continue; // no event, no trace entry
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
                // The frontier op may itself be a skipped SendIf whose guard resolves only
                // later — replay already skipped those; find the first op at/after `frontier`
                // that emits under the resolved vals.
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
    /// Sound over-approximation: for every op at/after the frontier, include every label it
    /// could produce under ANY assignment of still-unresolved guards. A guard already
    /// resolved narrows the set; an unresolved (or ⊥-valued) one contributes all variants.
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
                Op::Nondet => out.push(Label::nondet(["a", "b"])),
                Op::Send { .. } => out.push(op_label(op, &vals)),
                Op::SendIf { guard, eq, .. } => match vals[*guard] {
                    Some(v) if resolve(v) != *eq => {} // definitely skipped
                    _ => out.push(op_label(op, &vals)), // may emit
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
                        // Unresolved guard: both windows are possible.
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
                                // The guard may resolve to any payload the corpus uses
                                // ("g" included — the victim's gated send), or to no value.
                                for p in ["a", "b", "g", "__none__"] {
                                    out.push(mk(Pred::eq(p)));
                                }
                            }
                        },
                    }
                }
            }
        }
        Some(out)
    }
}

// -- Generator ------------------------------------------------------------------------------

/// A near-tie delivery window (bands overlapping within 1–2 ticks) plus one late band.
fn win(rng: &mut Rng) -> (u64, u64) {
    match rng.below(5) {
        0 => (0, 1),
        1 => (1, 2),
        2 => (2, 3),
        3 => (0, 4),
        _ => (5, 6), // late: genuinely unreadable next to an unread (0,1) competitor
    }
}

fn model(rng: &mut Rng) -> Model {
    if rng.chance(50) {
        Model::Asyn
    } else {
        Model::P2p
    }
}

fn payload(rng: &mut Rng) -> &'static str {
    if rng.chance(50) {
        "a"
    } else {
        "b"
    }
}

/// One random send-ish op; guards reference `producers` (value-producing op indices so far).
fn gen_send(rng: &mut Rng, nt: usize, victim: usize, producers: &[usize]) -> Op {
    // Destination bias onto the victim thread: racing sends need a shared receiver. Kept
    // moderate — relay threads (recv → send) need incoming traffic too, or their late sends
    // (the only source of backward revisits under DES drain-first) never fire.
    let dst = if rng.chance(40) { victim } else { rng.below(nt) };
    let (lo, hi) = win(rng);
    let m = model(rng);
    let v = payload(rng);
    if !producers.is_empty() && rng.chance(55) {
        let guard = producers[rng.below(producers.len())];
        let eq = payload(rng);
        if rng.chance(50) {
            Op::SendIf {
                guard,
                eq,
                dst,
                model: m,
                val: v,
                lo,
                hi,
            }
        } else {
            let (lo2, hi2) = win(rng);
            Op::SendWin {
                guard,
                eq,
                dst,
                model: m,
                val: v,
                lo1: lo,
                hi1: hi,
                lo2,
                hi2,
            }
        }
    } else {
        Op::Send {
            dst,
            model: m,
            val: v,
            lo,
            hi,
        }
    }
}

fn gen_recv(rng: &mut Rng, producers: &[usize]) -> Op {
    let sel = match rng.below(10) {
        0..=3 => Sel::Any,
        4..=6 => Sel::Eq(payload(rng)),
        _ if !producers.is_empty() => Sel::EqGuard(producers[rng.below(producers.len())]),
        _ => Sel::Any,
    };
    Op::Recv {
        sel,
        blocking: rng.chance(70),
    }
}

/// One random program: 3–4 threads, 2–4 ops each; the last thread is the "victim", biased
/// into the consumed-competitor shape: two sequential receives followed by a value-gated
/// send (the read value decides the emission — the raft LEADER shape).
fn gen_program(rng: &mut Rng) -> VdProgram {
    let nt = 3 + rng.below(2);
    let victim = nt - 1;
    let mut threads = Vec::with_capacity(nt);
    for t in 0..nt - 1 {
        let mut ops: Vec<Op> = Vec::new();
        let mut producers: Vec<usize> = Vec::new();
        if rng.chance(60) {
            producers.push(ops.len());
            ops.push(Op::Nondet);
        }
        let _ = t;
        let ne = 1 + rng.below(3);
        for _ in 0..ne {
            match rng.below(100) {
                // A mid-thread nondet: po-after a receive it lands in `Deleted` of later
                // revisits (a nondet at op 0 is drained first by DES and is almost never
                // deleted) — this is what exercises the PASS oracle.
                0..=19 => {
                    producers.push(ops.len());
                    ops.push(Op::Nondet);
                }
                20..=64 => ops.push(gen_send(rng, nt, victim, &producers)),
                _ => {
                    // A recv guard may only reference EARLIER producers, so the fresh index
                    // is pushed after generating the op.
                    let op = gen_recv(rng, &producers);
                    producers.push(ops.len());
                    ops.push(op);
                }
            }
        }
        threads.push(ops);
    }
    // The victim thread.
    let mut ops: Vec<Op> = Vec::new();
    let mut producers: Vec<usize> = Vec::new();
    if rng.chance(40) {
        producers.push(ops.len());
        ops.push(Op::Nondet);
    }
    producers.push(ops.len());
    ops.push(Op::Recv {
        sel: Sel::Any,
        blocking: true,
    });
    if rng.chance(70) {
        // A nondet BETWEEN the two receives: po-after a blocking receive, so it sits in the
        // `Deleted` set of any revisit of that receive — the main PASS-oracle trigger.
        producers.push(ops.len());
        ops.push(Op::Nondet);
    }
    if rng.chance(80) {
        let op = gen_recv(rng, &producers);
        producers.push(ops.len());
        ops.push(op);
    }
    if rng.chance(70) {
        // The value-gated downstream send: emitted only for one read value.
        let guard = producers[rng.below(producers.len())];
        let (lo, hi) = win(rng);
        ops.push(Op::SendIf {
            guard,
            eq: payload(rng),
            dst: rng.below(nt - 1),
            model: model(rng),
            val: "g",
            lo,
            hi,
        });
    }
    threads.push(ops);
    VdProgram { threads }
}

/// A directed scaffold guaranteeing the PASS oracle fires (the §3.3 ingredients, randomized
/// in windows/models/payloads): a victim with `recv; nd; [SendIf]; recv; [SendIf]`, an early
/// sender racing a **relay** whose send is po-after its own receive — the only kind of send
/// that is late under DES drain-first and therefore backward-revisits the victim, deleting
/// the mid-nondet (a non-min holder in half the branches ⇒ an oracle call).
fn gen_scaffold(rng: &mut Rng) -> VdProgram {
    let nt = 4;
    let victim = 0usize;
    // T0 (victim): recv; nd; [SendIf gated by nd]; recv; [SendIf gated by a read].
    let mut t0: Vec<Op> = vec![
        Op::Recv {
            sel: Sel::Any,
            blocking: true,
        },
        Op::Nondet,
    ];
    if rng.chance(50) {
        // A value-gated early send between the nondet and the second receive: under one
        // value the region carries an extra competitor — the feasibility-divergence seed.
        let (lo, hi) = win(rng);
        t0.push(Op::SendIf {
            guard: 1,
            eq: payload(rng),
            dst: 1 + rng.below(nt - 1),
            model: model(rng),
            val: payload(rng),
            lo,
            hi,
        });
    }
    let second = t0.len();
    t0.push(Op::Recv {
        sel: if rng.chance(50) { Sel::Any } else { Sel::EqGuard(1) },
        blocking: true,
    });
    if rng.chance(60) {
        let (lo, hi) = win(rng);
        t0.push(Op::SendIf {
            guard: if rng.chance(50) { 1 } else { second },
            eq: payload(rng),
            dst: 1 + rng.below(nt - 1),
            model: model(rng),
            val: "g",
            lo,
            hi,
        });
    }
    // T1: the early sender racing the relay for the victim's receives.
    let (lo, hi) = win(rng);
    let t1 = vec![Op::Send {
        dst: victim,
        model: model(rng),
        val: payload(rng),
        lo,
        hi,
    }];
    // T2 (relay): recv(=x) then send to the victim — late by construction.
    let (lo, hi) = win(rng);
    let t2 = vec![
        Op::Recv {
            sel: Sel::Eq("x"),
            blocking: true,
        },
        Op::Send {
            dst: victim,
            model: model(rng),
            val: payload(rng),
            lo,
            hi,
        },
    ];
    // T3: feeds the relay.
    let (lo, hi) = win(rng);
    let t3 = vec![Op::Send {
        dst: 2,
        model: model(rng),
        val: "x",
        lo,
        hi,
    }];
    VdProgram {
        threads: vec![t0, t1, t2, t3],
    }
}

// -- The recorded viable calls (O2 instrumentation) -----------------------------------------

type ViableCall = (ExecutionGraph, EventId, Val, EventId, Label, bool);

#[derive(Default)]
struct ViableRecorder {
    calls: Mutex<Vec<ViableCall>>,
}

impl Observer for ViableRecorder {
    fn on_viable_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        v: Val,
        revisiting: EventId,
        rev_label: &Label,
        verdict: bool,
    ) {
        self.calls.lock().unwrap().push((
            base.clone(),
            ep,
            v,
            revisiting,
            rev_label.clone(),
            verdict,
        ));
    }
}

// -- Per-program checks ---------------------------------------------------------------------

#[derive(Default)]
struct ProgStats {
    /// The oracle was exercised (≥ 1 viable call = a non-min holder under test).
    oracle_called: bool,
    /// Some viable call returned false (the oracle actually rejected something).
    oracle_rejected: bool,
    /// The time filter suppressed ≥ 1 terminal.
    filtered: bool,
    /// Dead Visit nodes of the T2 run (recorded, not asserted 0 — inexact closures allowed).
    dead: usize,
}

fn check_program(case: usize, prog: &VdProgram) -> ProgStats {
    let nt = prog.threads.len();
    let mut stats = ProgStats::default();

    // 1. T1-filter across every priority permutation: the reference partition.
    let mut reference: Option<(BTreeSet<String>, BTreeSet<String>, BTreeSet<String>)> = None;
    for perm in permutations(nt) {
        let obs = (CountingObserver::new(), ExecutionCollector::new());
        explore(
            || prog.clone(),
            &obs,
            Config::default()
                .collect_errors()
                .with_time_filter()
                .with_priorities(perm.clone()),
        );
        let (cnt, col) = &obs;
        let full: BTreeSet<String> = col.full_keys().into_iter().collect();
        let term_vec = col.terminal_keys();
        let term: BTreeSet<String> = term_vec.iter().cloned().collect();
        let filt: BTreeSet<String> = col.filtered_keys().into_iter().collect();
        assert_eq!(
            term_vec.len(),
            term.len(),
            "case {case} perm {perm:?}: duplicate T1 terminals\n{prog:#?}"
        );
        stats.filtered |= cnt.filtered() > 0;
        match &reference {
            None => reference = Some((full, term, filt)),
            Some((rf, rt, ri)) => {
                assert_eq!(&full, rf, "case {case} perm {perm:?}: T1 full varies\n{prog:#?}");
                assert_eq!(&term, rt, "case {case} perm {perm:?}: T1 term varies\n{prog:#?}");
                assert_eq!(&filt, ri, "case {case} perm {perm:?}: T1 filt varies\n{prog:#?}");
            }
        }
    }
    let (rf_full, rf_term, rf_filt) = reference.expect("≥1 permutation");

    // 2. Zombie == T1 exactly (one run — priority-invariant by construction).
    {
        let col = ExecutionCollector::new();
        explore(
            || prog.clone(),
            &col,
            Config::default().collect_errors().with_time_zombie(),
        );
        let full: BTreeSet<String> = col.full_keys().into_iter().collect();
        let term: BTreeSet<String> = col.terminal_keys().into_iter().collect();
        let filt: BTreeSet<String> = col.filtered_keys().into_iter().collect();
        assert_eq!(full, rf_full, "case {case}: zombie full != T1\n{prog:#?}");
        assert_eq!(term, rf_term, "case {case}: zombie term != T1\n{prog:#?}");
        assert_eq!(filt, rf_filt, "case {case}: zombie filt != T1\n{prog:#?}");
    }

    // 3+4. T2-oracle under two permutations: realizable == T1, no-dup, dead recorded; every
    // recorded viable verdict is cross-checked against the brute force (O2).
    let mut perms = vec![(0..nt).collect::<Vec<usize>>()];
    perms.push((0..nt).rev().collect());
    for perm in perms {
        let obs = (
            ExecutionCollector::new(),
            (DeadBranchDetector::new(), ViableRecorder::default()),
        );
        explore(
            || prog.clone(),
            &obs,
            Config::default()
                .collect_errors()
                .with_time_predicate()
                .with_priorities(perm.clone()),
        );
        let (col, (dead, recorder)) = &obs;

        let full: BTreeSet<String> = col.full_keys().into_iter().collect();
        let term_vec = col.terminal_keys();
        let term: BTreeSet<String> = term_vec.iter().cloned().collect();
        assert_eq!(
            term_vec.len(),
            term.len(),
            "case {case} perm {perm:?}: duplicate T2 terminals (O4)\n{prog:#?}"
        );
        assert_eq!(
            full, rf_full,
            "case {case} perm {perm:?}: T2 full != T1 realizable (C1)\n{prog:#?}"
        );
        assert_eq!(
            term, rf_term,
            "case {case} perm {perm:?}: T2 term != T1 realizable (C1)\n{prog:#?}"
        );
        stats.dead += dead.dead();

        // O2: dedupe by (base key, value, revisiting, label key) then diff each verdict.
        let calls = recorder.calls.lock().unwrap();
        let mut seen: BTreeMap<(String, String, EventId, String), bool> = BTreeMap::new();
        for (base, ep, v, revisiting, rev_label, verdict) in calls.iter() {
            stats.oracle_called = true;
            if !*verdict {
                stats.oracle_rejected = true;
            }
            let dedup_key = (
                base.canonical_key(),
                resolve(*v).to_string(),
                *revisiting,
                format!("{rev_label:?}"),
            );
            if let Some(&prev) = seen.get(&dedup_key) {
                assert_eq!(
                    prev, *verdict,
                    "case {case}: same viable call, different verdicts\n{prog:#?}"
                );
                continue;
            }
            seen.insert(dedup_key, *verdict);
            let brute = brute_viable(base, *ep, *v, prog, &perm, *revisiting, rev_label);
            assert_eq!(
                *verdict, brute,
                "case {case} perm {perm:?}: viable({}) = {verdict} but brute force says \
                 {brute} (ep {ep}, s {revisiting})\n{prog:#?}",
                resolve(*v)
            );
        }
    }

    stats
}

// -- Corpus drivers -------------------------------------------------------------------------

struct CorpusStats {
    progs: usize,
    oracle_called: usize,
    oracle_rejected: usize,
    with_filtered: usize,
    dead_total: usize,
}

fn run_corpus(seed: u64, n_progs: usize) -> CorpusStats {
    let mut rng = Rng::new(seed);
    let mut stats = CorpusStats {
        progs: n_progs,
        oracle_called: 0,
        oracle_rejected: 0,
        with_filtered: 0,
        dead_total: 0,
    };
    for case in 0..n_progs {
        // Every third program is a directed revisit scaffold; the rest are random soup.
        let prog = if case % 3 == 2 {
            gen_scaffold(&mut rng)
        } else {
            gen_program(&mut rng)
        };
        let s = check_program(case, &prog);
        stats.oracle_called += usize::from(s.oracle_called);
        stats.oracle_rejected += usize::from(s.oracle_rejected);
        stats.with_filtered += usize::from(s.filtered);
        stats.dead_total += s.dead;
    }
    stats
}

/// Fast value-dependent corpus. Non-degeneracy floors are pinned from the observed run and
/// guard the corpus against silently going value-independent (the SeqProgram blind spot).
#[test]
fn fuzz_value_dependent_small_corpus() {
    let s = run_corpus(0x7D5E_ED01, 120);
    assert_eq!(s.progs, 120);
    println!(
        "value-dependent corpus: oracle_called={}/{} oracle_rejected={} filtered={} dead={}",
        s.oracle_called, s.progs, s.oracle_rejected, s.with_filtered, s.dead_total
    );
    assert!(
        s.with_filtered >= 10,
        "too few programs with a filtered terminal ({}/120)",
        s.with_filtered
    );
    assert!(
        s.oracle_called >= 15,
        "the viable oracle was exercised on only {}/120 programs — the corpus stopped \
         producing non-min Deleted nondets (observed rate ~29/120)",
        s.oracle_called
    );
    // `oracle_rejected` is a printed stat, not a floor: false verdicts are rare in random
    // soup by construction; the directed false-path coverage lives in tests/viable.rs (m4/m5)
    // and in the raft `--faults 1` / `--bug` oracles.
}

/// Larger corpus, release-only.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: 400-program value-dependent corpus; run with --release"
)]
fn fuzz_value_dependent_large_corpus() {
    let s = run_corpus(0x7D5E_ED02, 400);
    assert_eq!(s.progs, 400);
    println!(
        "value-dependent corpus: oracle_called={}/{} oracle_rejected={} filtered={} dead={}",
        s.oracle_called, s.progs, s.oracle_rejected, s.with_filtered, s.dead_total
    );
    assert!(s.with_filtered >= 30, "filtered {}/400", s.with_filtered);
    assert!(s.oracle_called >= 50, "oracle_called {}/400", s.oracle_called);
}
