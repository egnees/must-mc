//! REVIEW ARTEFACT for phase H1 (not part of H1; delete or promote before merge).
//!
//! Keeps the one machine-checked finding of the H1 review that needs no instrumentation:
//! **the value-dependent table program violates the positional half of the
//! `Program::possible_future` contract that H1 documented and that `force_source` (3b) relies on
//! (`future.iter().skip(1)`).** H1's write-up claims "all existing implementations accidentally
//! honoured it"; they do not.
//!
//! # The line-6 (nondet) T-GATE experiment, and its outcome
//!
//! H1 originally also gated line 6 (`Explorer::visit_nondet`) on `time::gate_feasible`. The
//! review rejected it (F1): `visit_send` runs `backward_revisits` on `g_add` *unconditionally*
//! (A2.1b), so gating line 9 drops only the forward child, whereas a `continue` on line 6 drops
//! the arm before its forced sends exist — and with them the revisits of the first such send `w`,
//! which is exactly the canonical repair (`r ← w` consumes `w`, so it stops being a competitor)
//! for the infeasibility that triggered the rejection. Supporting facts: on line 6 the fallback
//! branch always returns `true` (`Builder::emit` skips nondet ⇒ `check(g + nd(v)) ≡ check(g)`),
//! every rejection is 2-hop (post-revisit, the region A2.2e declares OPEN), and on raft each
//! pruned subtree was a single barren Visit node.
//!
//! The gate was removed. Measured cost of removing it (raft, `--threads 1`; terminal sets
//! unchanged in every configuration): dead branches go back to **6 / 695** (`--faults 1`) and
//! **36 / 12280** (`--bug --timeouts 100,105,200`), i.e. `dead = 0` was bought entirely by the
//! rejected gate. That residual is the accepted price of the completeness-first priority.
//!
//! To re-run the A/B, re-add the gate behind an `if std::env::var_os("REVIEW_ND_GATE_OFF")
//! .is_none() { continue; }` escape hatch and diff the "time-realizable" / "dead branches" lines.
//!
mod hunt_common;

use hunt_common::*;
use must::event::Model;
use must::Program;

/// H1 documented a *positional* half of the `Program::possible_future` contract — "`labels[0]`
/// is exactly the thread's next label" — and claimed every existing implementation already
/// honoured it. They did not (review finding F7): the value-dependent table program
/// (`tests/fuzz_value_dependent.rs`, `tests/cb1_repro.rs`, `tests/gamma4_repro.rs`,
/// `tests/hunt_common/`) broke it in two shapes — `Op::SendWin` with an unresolved guard, and
/// `Op::Recv { sel: Sel::EqGuard(k) }` with `vals[k] == None` — because `possible_future` listed
/// *several* labels for the frontier op while `next` reports one. `force_source` condition (3b)
/// does `.skip(1)` on the strength of that contract, so a violation there is an **over-force**,
/// i.e. completeness loss.
///
/// It was vacuous at (3b) only by a coincidence of the corpus (the mismatching blocking receive
/// has predicate `Pred::eq("__none__")`, which no payload satisfies, so `force_source` bails at
/// condition (1)) — not by any stated property.
///
/// Fixed by deriving the head from the same `op_label` call `next` uses. This test now pins the
/// fix in both shapes; the permanent guard is the `debug_assert` on `future.first()` inside
/// `force_source` itself.
#[test]
fn vd_program_head_of_possible_future_is_the_next_label() {
    // Control: with the guard resolved, head == next.
    let prog = VdProgram {
        threads: vec![vec![
            Op::Nondet,
            Op::SendWin {
                guard: 0,
                eq: "a",
                dst: 1,
                model: Model::Asyn,
                val: "m",
                lo1: 0,
                hi1: 0,
                lo2: 40,
                hi2: 40,
            },
        ]],
    };
    let trace = vec![Some(must::Val::from("b"))];
    let next = prog.next(std::slice::from_ref(&trace)).remove(0);
    let future = prog.possible_future(0, &trace).expect("exact future");
    assert_eq!(
        future.first().cloned(),
        next.label().cloned(),
        "resolved guard: head is fine"
    );

    // Shape 1 (used to violate): an unresolved guard on `SendWin`. `next` reports the *else*
    // window `[40,40]` (`guard_hits` is false for `None`); `possible_future` still lists *both*
    // windows, but only from index 1 on — index 0 must be the `[40,40]` one.
    let prog2 = VdProgram {
        threads: vec![vec![
            Op::Recv {
                sel: Sel::Any,
                blocking: false,
            },
            Op::SendWin {
                guard: 0,
                eq: "a",
                dst: 1,
                model: Model::Asyn,
                val: "m",
                lo1: 0,
                hi1: 0,
                lo2: 40,
                hi2: 40,
            },
        ]],
    };
    let trace2 = vec![None]; // the nb-recv read ⊥ ⇒ the guard has no value
    let next2 = prog2.next(std::slice::from_ref(&trace2)).remove(0);
    let future2 = prog2.possible_future(0, &trace2).expect("exact future");
    assert_eq!(
        future2.first().cloned(),
        next2.label().cloned(),
        "unresolved SendWin guard: head must be the label `next` reports, not the first \
         over-approximation alternative"
    );
    // ... and the head is the *only* thing the fix pins: the tail stays whatever sound
    // over-approximation the program wants for the events after it (here: nothing follows).
    assert_eq!(future2.len(), 1, "one op left, so one label");

    // Shape 2 (used to violate): an unresolved `EqGuard` receive. `next` reports
    // `Pred::eq("__none__")`; `possible_future` used to list every payload first.
    let prog3 = VdProgram {
        threads: vec![vec![
            Op::Recv {
                sel: Sel::Any,
                blocking: false,
            },
            Op::Recv {
                sel: Sel::EqGuard(0),
                blocking: true,
            },
        ]],
    };
    let trace3 = vec![None]; // the nb-recv read ⊥ ⇒ the guard has no value
    let next3 = prog3.next(std::slice::from_ref(&trace3)).remove(0);
    let future3 = prog3.possible_future(0, &trace3).expect("exact future");
    assert_eq!(
        future3.first().cloned(),
        next3.label().cloned(),
        "unresolved EqGuard receive: head must be the label `next` reports"
    );

    // A finished thread's exact future is empty.
    let trace_done = vec![None, Some(must::Val::from("a"))];
    assert!(prog3
        .next(std::slice::from_ref(&trace_done))
        .remove(0)
        .is_finished());
    assert_eq!(prog3.possible_future(0, &trace_done), Some(Vec::new()));
}
