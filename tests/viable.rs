//! O2 units for the existential `viable(v)` oracle (T2_ORACLE_SPEC §1.3, Part 4 step 3):
//! the DFS verdict is diffed against an independent brute-force enumeration of ALL forward
//! completions (every interleaving, every resolution, no drain, no pruning, no memo) on tiny
//! **value-dependent** mock programs — the class `SeqProgram` structurally cannot express.
//!
//! The mocks implement an *exact* `possible_future`, so `gate_feasible`'s forced-closure is
//! exact and the two searches share one visitability predicate (O3); with an inexact future
//! `viable` deliberately under-approximates (quiescence-only success testing — the safe
//! direction: duplicates, never completeness loss), and the diff would not be meaningful.

use std::collections::{BTreeMap, VecDeque};

use must::event::{EventId, Label, Model, Pred, Window};
use must::graph::ExecutionGraph;
use must::time::{check, gate_feasible, viable, ViableMemo};
use must::{consistent, traces_of, Program, ThreadNext, Val};

// -- A tiny value-dependent program vehicle -----------------------------------------------

/// Per-thread `next` function of the thread's own trace.
type NextFn = fn(&[Option<Val>]) -> ThreadNext;
/// Per-thread `possible_future` function of the thread's own trace.
type FutureFn = fn(&[Option<Val>]) -> Option<Vec<Label>>;

/// Table of per-thread `next` / `possible_future` functions of the thread's own trace.
struct Vdp {
    nexts: Vec<NextFn>,
    futures: Vec<FutureFn>,
}

impl Program for Vdp {
    fn num_threads(&self) -> usize {
        self.nexts.len()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..self.nexts.len())
            .map(|i| (self.nexts[i])(&traces[i]))
            .collect()
    }
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        (self.futures[tid])(trace)
    }
}

fn val(s: &str) -> Val {
    Val::from(s)
}
fn is(entry: &Option<Val>, s: &str) -> bool {
    entry.as_ref() == Some(&val(s))
}

// -- Independent brute force ---------------------------------------------------------------

/// Every consistent state forward-reachable from `h0`: from each state, each thread's next
/// event is resolved every legal way (send/error added; nondet at every value; a receive at
/// every present send and ⊥ — reading `revisiting` included). BFS over contents, deduped by
/// canonical key. No feasibility pruning, no drain ordering, no memo — fully independent of
/// the `viable` search structure.
fn all_states<P: Program>(h0: &ExecutionGraph, program: &P) -> Vec<ExecutionGraph> {
    let n = program.num_threads();
    let mut seen: BTreeMap<String, ExecutionGraph> = BTreeMap::new();
    let mut queue: VecDeque<ExecutionGraph> = VecDeque::new();
    if consistent(h0) {
        seen.insert(h0.canonical_key(), h0.clone());
        queue.push_back(h0.clone());
    }
    while let Some(h) = queue.pop_front() {
        let traces = traces_of(&h, n);
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
                if !consistent(&c) {
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

/// Reference verdict: ∃ a reachable state where `revisiting` is present-unread with
/// `rev_label` and the state passes feasibility + the visitability gate (§1.4 success).
fn brute_viable<P: Program>(
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
            && check(h).is_feasible()
            && gate_feasible(h, program, priorities)
    })
}

/// Assert `viable == brute_viable == expected` for one `(mock, v)` case.
#[allow(clippy::too_many_arguments)]
fn diff_case(
    name: &str,
    base: &ExecutionGraph,
    ep: EventId,
    v: &str,
    program: &Vdp,
    revisiting: EventId,
    rev_label: &Label,
    expected: bool,
) {
    let priorities: Vec<usize> = (0..program.num_threads()).collect();
    let mut memo = ViableMemo::new();
    let got = viable(
        base,
        ep,
        val(v),
        program,
        &priorities,
        revisiting,
        rev_label,
        &mut memo,
    );
    let brute = brute_viable(base, ep, val(v), program, &priorities, revisiting, rev_label);
    assert_eq!(got, brute, "{name}[{v}]: viable disagrees with brute force");
    assert_eq!(got, expected, "{name}[{v}]: unexpected verdict");
}

// -- Mock 1+2: emission / label gating by the tested nondet itself -------------------------
//
// T0: ep = nd{a,b}; under `a` it emits send(1,"g") (the revisiting label), under `b` it emits
// send(1,"z") — the wrong label at the revisiting position (the mismatch cut).

fn m12_t0(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(Label::nondet(["a", "b"])),
        1 if is(&trace[0], "a") => ThreadNext::Next(Label::send(Model::Asyn, 1, "g")),
        1 => ThreadNext::Next(Label::send(Model::Asyn, 1, "z")),
        _ => ThreadNext::Finished,
    }
}
fn m12_t0_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![
            Label::nondet(["a", "b"]),
            Label::send(Model::Asyn, 1, "g"),
            Label::send(Model::Asyn, 1, "z"),
        ],
        1 if is(&trace[0], "a") => vec![Label::send(Model::Asyn, 1, "g")],
        1 => vec![Label::send(Model::Asyn, 1, "z")],
        _ => vec![],
    })
}
fn finished(_: &[Option<Val>]) -> ThreadNext {
    ThreadNext::Finished
}
fn empty_future(_: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(vec![])
}

#[test]
fn emission_and_mismatch_gating() {
    let prog = Vdp {
        nexts: vec![m12_t0, finished],
        futures: vec![m12_t0_future, empty_future],
    };
    let mut base = ExecutionGraph::new();
    let ep = base.add_event(0, Label::nondet(["a", "b"]));
    base.set_nd(ep, val("a")); // pre-pin; viable re-pins per call
    let revisiting = EventId::new(0, 1);
    let rev_label = Label::send(Model::Asyn, 1, "g");
    // Under `a` the send appears at (0,1) — viable; under `b` position (0,1) holds "z".
    diff_case("m12", &base, ep, "a", &prog, revisiting, &rev_label, true);
    diff_case("m12", &base, ep, "b", &prog, revisiting, &rev_label, false);
}

// -- Mock 3: deferral through ANOTHER thread's choice point --------------------------------
//
// T0: ep = nd{a,b} (inert — both values behave the same). T1: recv(=x); send(0,"g").
// T2: nd{p,q}; under `p` it emits send(1,"x"). The witness needs T2's branch resolved to `p`
// and its send drained BEFORE T1's receive can be resolved — the (thread × option) deferral.

fn m3_t1(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(Label::recv(Pred::eq("x"))),
        1 => ThreadNext::Next(Label::send(Model::Asyn, 0, "g")),
        _ => ThreadNext::Finished,
    }
}
fn m3_t1_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![Label::recv(Pred::eq("x")), Label::send(Model::Asyn, 0, "g")],
        1 => vec![Label::send(Model::Asyn, 0, "g")],
        _ => vec![],
    })
}
fn m3_t2(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(Label::nondet(["p", "q"])),
        1 if is(&trace[0], "p") => ThreadNext::Next(Label::send(Model::Asyn, 1, "x")),
        _ => ThreadNext::Finished,
    }
}
fn m3_t2_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![Label::nondet(["p", "q"]), Label::send(Model::Asyn, 1, "x")],
        1 if is(&trace[0], "p") => vec![Label::send(Model::Asyn, 1, "x")],
        _ => vec![],
    })
}
fn m3_t0(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(Label::nondet(["a", "b"])),
        _ => ThreadNext::Finished,
    }
}
fn m3_t0_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![Label::nondet(["a", "b"])],
        _ => vec![],
    })
}

#[test]
fn deferral_through_foreign_branch() {
    let prog = Vdp {
        nexts: vec![m3_t0, m3_t1, m3_t2],
        futures: vec![m3_t0_future, m3_t1_future, m3_t2_future],
    };
    let mut base = ExecutionGraph::new();
    let ep = base.add_event(0, Label::nondet(["a", "b"]));
    base.set_nd(ep, val("a"));
    let revisiting = EventId::new(1, 1);
    let rev_label = Label::send(Model::Asyn, 0, "g");
    // Both values are viable: the witness goes through T2 = p regardless of ep.
    diff_case("m3", &base, ep, "a", &prog, revisiting, &rev_label, true);
    diff_case("m3", &base, ep, "b", &prog, revisiting, &rev_label, true);
}

// -- Mock 4: a time-infeasible witness is rejected -----------------------------------------
//
// T0: send_within(2,"late",[40,60]). T1: ep = nd{a,b}; under `b` it also emits
// send_within(2,"early",[1,2]). T2: recv(any); if it read "late" → send(0,"g").
// Under `a` reading "late" is feasible (no competitor) and emits g. Under `b` the unread
// "early" competitor kills the late reading (B: avail(early) ≤ 2 < 40 ≤ avail(late); A: 40 > 0),
// and reading "early" diverges T2 away from emitting g — no viable witness at all.

fn m4_t0(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(Label::send_within(Model::Asyn, 2, "late", Window::new(40, 60))),
        _ => ThreadNext::Finished,
    }
}
fn m4_t0_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![Label::send_within(Model::Asyn, 2, "late", Window::new(40, 60))],
        _ => vec![],
    })
}
fn m4_t1(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(Label::nondet(["a", "b"])),
        1 if is(&trace[0], "b") => {
            ThreadNext::Next(Label::send_within(Model::Asyn, 2, "early", Window::new(1, 2)))
        }
        _ => ThreadNext::Finished,
    }
}
fn m4_t1_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![
            Label::nondet(["a", "b"]),
            Label::send_within(Model::Asyn, 2, "early", Window::new(1, 2)),
        ],
        1 if is(&trace[0], "b") => {
            vec![Label::send_within(Model::Asyn, 2, "early", Window::new(1, 2))]
        }
        _ => vec![],
    })
}
fn m4_t2(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(Label::recv(Pred::any())),
        1 if is(&trace[0], "late") => ThreadNext::Next(Label::send(Model::Asyn, 0, "g")),
        _ => ThreadNext::Finished,
    }
}
fn m4_t2_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![Label::recv(Pred::any()), Label::send(Model::Asyn, 0, "g")],
        1 if is(&trace[0], "late") => vec![Label::send(Model::Asyn, 0, "g")],
        _ => vec![],
    })
}

#[test]
fn time_infeasible_witness_rejected() {
    let prog = Vdp {
        nexts: vec![m4_t0, m4_t1, m4_t2],
        futures: vec![m4_t0_future, m4_t1_future, m4_t2_future],
    };
    let mut base = ExecutionGraph::new();
    let ep = base.add_event(1, Label::nondet(["a", "b"]));
    base.set_nd(ep, val("a"));
    let revisiting = EventId::new(2, 1);
    let rev_label = Label::send(Model::Asyn, 0, "g");
    diff_case("m4", &base, ep, "a", &prog, revisiting, &rev_label, true);
    diff_case("m4", &base, ep, "b", &prog, revisiting, &rev_label, false);
}

// -- Mock 5: a consumed competitor re-enables the late reading -----------------------------
//
// Like mock 4, but T2 has TWO receives and emits g only when the second read "late": under `b`
// the witness reads "early" first (consuming the competitor), then "late" — feasible; under `a`
// there is only one message, the second receive blocks forever, and g never appears.

fn m5_t2(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 | 1 => ThreadNext::Next(Label::recv(Pred::any())),
        2 if is(&trace[1], "late") => ThreadNext::Next(Label::send(Model::Asyn, 0, "g")),
        _ => ThreadNext::Finished,
    }
}
fn m5_t2_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 | 1 => vec![Label::recv(Pred::any()), Label::send(Model::Asyn, 0, "g")],
        2 if is(&trace[1], "late") => vec![Label::send(Model::Asyn, 0, "g")],
        _ => vec![],
    })
}

#[test]
fn consumed_competitor_enables_late_read() {
    let prog = Vdp {
        nexts: vec![m4_t0, m4_t1, m5_t2],
        futures: vec![m4_t0_future, m4_t1_future, m5_t2_future],
    };
    let mut base = ExecutionGraph::new();
    let ep = base.add_event(1, Label::nondet(["a", "b"]));
    base.set_nd(ep, val("a"));
    let revisiting = EventId::new(2, 2);
    let rev_label = Label::send(Model::Asyn, 0, "g");
    diff_case("m5", &base, ep, "a", &prog, revisiting, &rev_label, false);
    diff_case("m5", &base, ep, "b", &prog, revisiting, &rev_label, true);
}

// -- O1/O5: the verdict is priority-invariant and the memo pays off ------------------------

#[test]
fn verdict_priority_invariant_and_memo_hits() {
    let prog = Vdp {
        nexts: vec![m4_t0, m4_t1, m5_t2],
        futures: vec![m4_t0_future, m4_t1_future, m5_t2_future],
    };
    let mut base = ExecutionGraph::new();
    let ep = base.add_event(1, Label::nondet(["a", "b"]));
    base.set_nd(ep, val("a"));
    let revisiting = EventId::new(2, 2);
    let rev_label = Label::send(Model::Asyn, 0, "g");

    // O1: `priorities` must not change the verdict (they only reach gate_feasible).
    let mut verdicts = Vec::new();
    for perm in [[0, 1, 2], [2, 1, 0], [1, 2, 0]] {
        let mut memo = ViableMemo::new();
        verdicts.push(viable(
            &base, ep, val("b"), &prog, &perm, revisiting, &rev_label, &mut memo,
        ));
    }
    assert!(
        verdicts.iter().all(|&v| v == verdicts[0]),
        "viable verdict varies with priorities: {verdicts:?}"
    );

    // O5: a shared memo answers the repeat call from cache (hits strictly grow, same verdict).
    let priorities = [0, 1, 2];
    let mut memo = ViableMemo::new();
    let first = viable(
        &base, ep, val("b"), &prog, &priorities, revisiting, &rev_label, &mut memo,
    );
    let (h0, m0) = (memo.hits(), memo.misses());
    let second = viable(
        &base, ep, val("b"), &prog, &priorities, revisiting, &rev_label, &mut memo,
    );
    assert_eq!(first, second);
    assert!(memo.hits() > h0, "repeat call must hit the memo");
    assert_eq!(memo.misses(), m0, "repeat call must add no misses");
}
