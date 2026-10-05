//! Concrete oracle evidence, cache reconstruction, and bounded-query regressions.

mod common;

use common::SeqProgram;
use must::time::witness::{query, OracleBudget, OracleLimit, OracleOutcome, PinnedChoice};
use must::time::{viable, viable_recv, viable_recv_bot, ViableMemo};
use must::{EventId, ExecutionGraph, Label, Model, Pred, Program, ThreadNext, Val, Window};

fn send(model: Model, dst: usize, payload: &str, lo: u64, hi: u64) -> Label {
    Label::send_within(model, dst, payload, Window::new(lo, hi))
}

fn witness(outcome: OracleOutcome) -> must::time::witness::OracleWitness {
    match outcome {
        OracleOutcome::Witness(w) => w,
        other => panic!("expected concrete witness, got {other:?}"),
    }
}

#[test]
#[should_panic(expected = "ND pin value must belong to its option set")]
fn diagnostic_query_rejects_a_value_outside_the_nd_option_set() {
    let nd = Label::nondet(["a", "b"]);
    let goal = send(Model::Asyn, 0, "goal", 1, 1);
    let program = SeqProgram::new(vec![vec![nd.clone()], vec![goal.clone()]]);
    let mut base = ExecutionGraph::new();
    let ep = base.add_event(0, nd);
    base.set_nd(ep, "a".into());
    query(
        &base,
        PinnedChoice::Nondet {
            event: ep,
            value: "c".into(),
        },
        &program,
        &[0, 1],
        EventId::new(1, 0),
        &goal,
        &mut ViableMemo::new(),
        OracleBudget::default(),
    );
}

#[test]
fn initially_ready_target_needs_only_a_drain_and_preserves_original_base() {
    for model in [Model::Asyn, Model::P2p] {
        let nd = Label::nondet(["a", "b"]);
        let goal = send(model, 0, "goal", 2, 3);
        let program = SeqProgram::new(vec![vec![nd.clone()], vec![goal.clone()]]);
        let mut base = ExecutionGraph::new();
        let ep = base.add_event(0, nd);
        base.set_nd(ep, "b".into());
        let before = base.canonical_key();
        let target = EventId::new(1, 0);
        let choice = PinnedChoice::Nondet {
            event: ep,
            value: "a".into(),
        };
        let w = witness(query(
            &base,
            choice,
            &program,
            &[0, 1],
            target,
            &goal,
            &mut ViableMemo::new(),
            OracleBudget::default(),
        ));
        assert_eq!(w.choice(), choice);
        assert_eq!(w.target(), target);
        assert_eq!(w.target_label(), &goal);
        assert_eq!(w.base().canonical_key(), before);
        assert_eq!(base.canonical_key(), before);
        assert_eq!(w.graph().nd_value(ep), Some(&"a".into()));
        assert!(w.stats().target_initially_ready);
        assert_eq!(w.stats().states, 1);
        assert_eq!(w.stats().drain_added, 1);
        assert_eq!(w.stats().branch_states, 0);
        assert_eq!(w.stats().branch_children, 0);
        assert!(w.recheck(&program));
        let changed = SeqProgram::new(vec![vec![Label::nondet(["a", "b"])], vec![]]);
        assert!(!w.recheck(&changed));
    }
}

fn branching_program() -> (SeqProgram, ExecutionGraph, EventId, EventId, Label) {
    let inert = Label::nondet(["a", "b"]);
    let goal = send(Model::Asyn, 0, "goal", 2, 3);
    let program = SeqProgram::new(vec![
        vec![inert.clone()],
        vec![Label::recv(Pred::eq("go")), goal.clone()],
        vec![Label::nondet(["x", "y"]), send(Model::Asyn, 1, "go", 5, 10)],
    ]);
    let mut base = ExecutionGraph::new();
    let ep = base.add_event(0, inert);
    base.set_nd(ep, "a".into());
    (program, base, ep, EventId::new(1, 1), goal)
}

#[test]
fn positive_bool_cache_reconstructs_real_nd_and_rf_continuation() {
    let (program, base, ep, target, goal) = branching_program();
    let mut memo = ViableMemo::new();
    assert!(viable(
        &base,
        ep,
        "a".into(),
        &program,
        &[0, 1, 2],
        target,
        &goal,
        &mut memo,
    ));
    let w = witness(query(
        &base,
        PinnedChoice::Nondet {
            event: ep,
            value: "a".into(),
        },
        &program,
        &[0, 1, 2],
        target,
        &goal,
        &mut memo,
        OracleBudget::default(),
    ));
    assert!(!w.stats().target_initially_ready);
    assert!(w.stats().positive_cache_reconstructions > 0);
    assert!(w.stats().branch_states >= 2);
    assert!(w.stats().branch_children >= 2);
    assert_eq!(w.graph().nd_value(EventId::new(2, 0)), Some(&"x".into()));
    assert_eq!(
        w.graph().reads_from(EventId::new(1, 0)),
        Some(EventId::new(2, 1))
    );
    assert!(w.graph().contains(target));
    assert!(!w.graph().is_read(target));
    assert!(w.recheck(&program));
}

#[test]
fn budget_exhaustion_is_unknown_and_does_not_cache_false() {
    let (program, base, ep, target, goal) = branching_program();
    for budget in [
        OracleBudget {
            max_states: 0,
            max_added_events: 100,
        },
        OracleBudget {
            max_states: 1,
            max_added_events: 100,
        },
        OracleBudget {
            max_states: 100,
            max_added_events: 0,
        },
        OracleBudget {
            max_states: 100,
            max_added_events: 2,
        },
    ] {
        let mut memo = ViableMemo::new();
        let outcome = query(
            &base,
            PinnedChoice::Nondet {
                event: ep,
                value: "a".into(),
            },
            &program,
            &[0, 1, 2],
            target,
            &goal,
            &mut memo,
            budget,
        );
        assert_eq!(outcome.verdict(), None);
        let OracleOutcome::Unknown(unknown) = outcome else {
            unreachable!()
        };
        assert!(unknown.stats.states <= budget.max_states);
        assert!(unknown.stats.added_events <= budget.max_added_events);
        assert!(matches!(
            unknown.limit,
            OracleLimit::States | OracleLimit::AddedEvents
        ));
        assert!(viable(
            &base,
            ep,
            "a".into(),
            &program,
            &[0, 1, 2],
            target,
            &goal,
            &mut memo,
        ));
    }
}

#[test]
fn positive_cache_with_insufficient_reconstruction_budget_returns_unknown() {
    let (program, base, ep, target, goal) = branching_program();
    let mut memo = ViableMemo::new();
    assert!(viable(
        &base,
        ep,
        "a".into(),
        &program,
        &[0, 1, 2],
        target,
        &goal,
        &mut memo,
    ));
    let outcome = query(
        &base,
        PinnedChoice::Nondet {
            event: ep,
            value: "a".into(),
        },
        &program,
        &[0, 1, 2],
        target,
        &goal,
        &mut memo,
        OracleBudget {
            max_states: 1,
            max_added_events: 100,
        },
    );
    assert_eq!(outcome.verdict(), None);
    assert_eq!(outcome.stats().positive_cache_reconstructions, 1);
    assert!(viable(
        &base,
        ep,
        "a".into(),
        &program,
        &[0, 1, 2],
        target,
        &goal,
        &mut memo,
    ));
}

struct ReceiveBranch;

impl Program for ReceiveBranch {
    fn num_threads(&self) -> usize {
        2
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        let sends = [
            send(Model::Asyn, 1, "red", 5, 10),
            send(Model::Asyn, 1, "blue", 5, 10),
        ];
        let t0 = sends
            .get(traces[0].len())
            .cloned()
            .map_or(ThreadNext::Finished, ThreadNext::Next);
        let t1 = match traces[1].len() {
            0 => ThreadNext::Next(Label::recv(Pred::any())),
            1 => ThreadNext::Next(send(
                Model::Asyn,
                0,
                if traces[1][0] == Some("red".into()) {
                    "goal"
                } else {
                    "wrong"
                },
                2,
                3,
            )),
            _ => ThreadNext::Finished,
        };
        vec![t0, t1]
    }
}

#[test]
fn receive_pins_follow_value_dependent_labels_and_negative_cache() {
    let program = ReceiveBranch;
    let mut base = ExecutionGraph::new();
    let red = base.add_event(0, send(Model::Asyn, 1, "red", 5, 10));
    let blue = base.add_event(0, send(Model::Asyn, 1, "blue", 5, 10));
    let ep = base.add_event(1, Label::recv(Pred::any()));
    base.set_rf(ep, Some(red));
    let target = EventId::new(1, 1);
    let goal = send(Model::Asyn, 0, "goal", 2, 3);
    for (source, expected) in [(red, true), (blue, false)] {
        let cold = query(
            &base,
            PinnedChoice::Receive {
                event: ep,
                source: Some(source),
            },
            &program,
            &[0, 1],
            target,
            &goal,
            &mut ViableMemo::new(),
            OracleBudget::default(),
        );
        assert_eq!(cold.verdict(), Some(expected));
        assert_eq!(cold.stats().drain_added, 1);
        let mut memo = ViableMemo::new();
        assert_eq!(
            viable_recv(
                &base,
                ep,
                source,
                &program,
                &[0, 1],
                target,
                &goal,
                &mut memo
            ),
            expected
        );
        let outcome = query(
            &base,
            PinnedChoice::Receive {
                event: ep,
                source: Some(source),
            },
            &program,
            &[0, 1],
            target,
            &goal,
            &mut memo,
            OracleBudget::default(),
        );
        assert_eq!(outcome.verdict(), Some(expected));
        if expected {
            let w = witness(outcome);
            assert!(w.recheck(&program));
            assert_eq!(w.graph().reads_from(ep), Some(red));
        } else {
            assert_eq!(outcome.stats().negative_cache_hits, 1);
            assert!(!outcome.stats().target_initially_ready);
        }
    }
}

#[test]
fn bottom_query_preserves_existing_nonblocking_semantics() {
    for blocking in [false, true] {
        let recv = if blocking {
            Label::recv(Pred::any())
        } else {
            Label::recv_nb(Pred::any())
        };
        let goal = send(Model::P2p, 0, "goal", 0, 0);
        let program = SeqProgram::new(vec![vec![recv.clone(), goal.clone()]]);
        let mut base = ExecutionGraph::new();
        let ep = base.add_event(0, recv);
        base.set_rf(ep, None);
        let target = EventId::new(0, 1);
        let mut memo = ViableMemo::new();
        let expected = viable_recv_bot(&base, ep, &program, &[0], target, &goal, &mut memo);
        assert_eq!(expected, !blocking);
        let outcome = query(
            &base,
            PinnedChoice::Receive {
                event: ep,
                source: None,
            },
            &program,
            &[0],
            target,
            &goal,
            &mut memo,
            OracleBudget::default(),
        );
        assert_eq!(outcome.verdict(), Some(expected));
        if expected {
            assert!(witness(outcome).recheck(&program));
        }
    }
}

#[test]
fn drain_runs_past_target_and_can_reject_the_final_quiescent_graph() {
    let victim = Label::recv(Pred::any());
    let slow = send(Model::Asyn, 0, "slow", 10, 10);
    let goal = send(Model::Asyn, 1, "goal", 2, 2);
    let killer = send(Model::Asyn, 0, "early", 2, 2);
    let nd = Label::nondet(["a", "b"]);
    let program = SeqProgram::new(vec![
        vec![victim.clone()],
        vec![slow.clone()],
        vec![nd.clone(), goal.clone(), killer],
    ]);
    let mut base = ExecutionGraph::new();
    let source = base.add_event(1, slow);
    let r = base.add_event(0, victim);
    base.set_rf(r, Some(source));
    let ep = base.add_event(2, nd);
    base.set_nd(ep, "a".into());
    let target = EventId::new(2, 1);
    let outcome = query(
        &base,
        PinnedChoice::Nondet {
            event: ep,
            value: "a".into(),
        },
        &program,
        &[0, 1, 2],
        target,
        &goal,
        &mut ViableMemo::new(),
        OracleBudget::default(),
    );
    assert_eq!(outcome.verdict(), Some(false));
    assert!(outcome.stats().target_initially_ready);
    assert_eq!(outcome.stats().drain_added, 2);
    assert_eq!(outcome.stats().branch_states, 0);
}
