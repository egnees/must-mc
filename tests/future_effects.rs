//! Certificate-specific regression tests; full graph-set comparisons live in
//! certified_time.rs. These target coverage, provenance, and inconclusive work.
use must::time::future::{
    check_completion, ChoiceGuard, CompletionCheck, LookaheadBudget, UnknownReason,
};
use must::{EventId, ExecutionGraph, Label, Model, Pred, Program, ThreadNext, Val, Window};

fn send(dst: usize, value: &str, at: u64) -> Label {
    Label::send_within(Model::Asyn, dst, value, Window::new(at, at))
}

fn victim() -> Label {
    Label::recv(Pred::new("early|slow", |value| {
        value == "early" || value == "slow"
    }))
}

fn relay() -> Label {
    Label::recv(Pred::new("red|blue", |value| {
        value == "red" || value == "blue"
    }))
}

struct Fork {
    always_early: bool,
}

impl Program for Fork {
    fn num_threads(&self) -> usize {
        4
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..4)
            .map(|tid| {
                let events = match tid {
                    0 => vec![send(1, "slow", 10)],
                    1 => vec![victim()],
                    2 => vec![send(3, "red", 1), send(3, "blue", 1)],
                    3 if traces[3].first() == Some(&Some("red".into())) => {
                        vec![relay(), send(1, "early", 0)]
                    }
                    3 if self.always_early => {
                        vec![relay(), send(1, "other", 0), send(1, "early", 0)]
                    }
                    3 => vec![relay(), send(1, "other", 0)],
                    _ => unreachable!(),
                };
                events
                    .get(traces[tid].len())
                    .cloned()
                    .map(ThreadNext::Next)
                    .unwrap_or(ThreadNext::Finished)
            })
            .collect()
    }
}

fn prefix() -> ExecutionGraph {
    let mut graph = ExecutionGraph::new();
    let slow = graph.add_event(0, send(1, "slow", 10));
    let receive = graph.add_event(1, victim());
    graph.set_rf(receive, Some(slow));
    graph.add_event(2, send(3, "red", 1));
    graph.add_event(2, send(3, "blue", 1));
    graph
}

#[test]
fn impossible_retains_disjoint_cases_and_revalidates_full_argument() {
    let graph = prefix();
    let original = graph.canonical_key();
    let bad = Fork { always_early: true };
    let CompletionCheck::Impossible(certificate) =
        check_completion(&graph, &bad, LookaheadBudget::default())
    else {
        panic!("both relay cases force an early competitor");
    };
    assert_eq!(certificate.cases().len(), 2);
    assert_eq!(certificate.coverage().len(), 1);
    assert_eq!(certificate.coverage()[0].alternatives().len(), 2);
    assert!(certificate.cases().iter().all(|case| case.recheck_timing()));
    for (index, case) in certificate.cases().iter().enumerate() {
        assert_eq!(
            case.guard(),
            &[ChoiceGuard::Receive {
                receive: EventId::new(3, 0),
                source: EventId::new(2, index),
            }]
        );
        assert_eq!(
            case.graph().reads_from(EventId::new(3, 0)),
            Some(EventId::new(2, index))
        );
    }
    // The blue case emits an unrelated message before its early message; retaining
    // complete guarded graphs preserves this identity and clock correlation.
    assert_eq!(certificate.cases()[0].graph().thread_len(3), 2);
    assert_eq!(certificate.cases()[1].graph().thread_len(3), 3);
    assert!(certificate.applies_to(&graph.clone()));
    assert!(certificate.revalidate(&graph, &bad));
    assert!(!certificate.revalidate(
        &graph,
        &Fork {
            always_early: false
        }
    ));
    let mut changed = graph.clone();
    changed.add_event(0, send(1, "unrelated", 30));
    assert!(!certificate.applies_to(&changed));
    let keep = graph
        .iter_events()
        .filter(|&event| event != EventId::new(1, 0))
        .collect();
    assert!(!certificate.applies_to(&graph.restrict(&keep)));
    assert_eq!(graph.canonical_key(), original);
}

#[test]
fn rejecting_one_case_does_not_hide_exhausted_coverage_budget() {
    let outcome = check_completion(
        &prefix(),
        &Fork { always_early: true },
        LookaheadBudget {
            max_states: 2,
            max_added_events: 64,
        },
    );
    assert!(outcome.stats().expanded_states > 0);
    assert!(outcome.stats().expanded_cases > 0);
    let CompletionCheck::Unknown(unknown) = outcome else {
        panic!("second case has not been checked");
    };
    assert_eq!(unknown.reason(), &UnknownReason::BudgetExhausted);
    assert!(unknown.stats().temporal_checks > 0);
}

struct HiddenSource {
    precise: bool,
}

impl HiddenSource {
    fn remaining(&self, tid: usize, trace: &[Option<Val>]) -> Vec<Label> {
        let events = match tid {
            0 => vec![send(1, "slow", 10)],
            1 => vec![victim()],
            2 => vec![send(3, "red", 1), send(4, "gate", 0)],
            3 if trace.is_empty() || trace[0] == Some("red".into()) => {
                vec![relay(), send(1, "early", 0)]
            }
            3 => vec![relay()],
            4 => vec![Label::recv(Pred::eq("gate")), send(3, "blue", 0)],
            _ => unreachable!(),
        };
        events.into_iter().skip(trace.len()).collect()
    }
}

impl Program for HiddenSource {
    fn num_threads(&self) -> usize {
        5
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..5)
            .map(|tid| {
                self.remaining(tid, &traces[tid])
                    .into_iter()
                    .next()
                    .map(ThreadNext::Next)
                    .unwrap_or(ThreadNext::Finished)
            })
            .collect()
    }
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        self.precise.then(|| self.remaining(tid, trace))
    }
}

#[test]
fn hidden_source_is_unknown_until_its_alphabet_exclusion_can_be_proved() {
    let mut graph = ExecutionGraph::new();
    let slow = graph.add_event(0, send(1, "slow", 10));
    let receive = graph.add_event(1, victim());
    graph.set_rf(receive, Some(slow));
    graph.add_event(2, send(3, "red", 1));
    graph.add_event(2, send(4, "gate", 0));
    let result = check_completion(
        &graph,
        &HiddenSource { precise: false },
        LookaheadBudget::default(),
    );
    let CompletionCheck::Unknown(unknown) = result else {
        panic!("present red source does not exhaust possible future blue sources");
    };
    assert!(matches!(
        unknown.reason(),
        UnknownReason::IncompleteSources { .. }
    ));
    let CompletionCheck::Witness(witness) = check_completion(
        &graph,
        &HiddenSource { precise: true },
        LookaheadBudget::default(),
    ) else {
        panic!("gate receive can reveal blue, whose source case avoids the early effect");
    };
    assert_eq!(
        witness.terminal_graph().reads_from(EventId::new(3, 0)),
        Some(EventId::new(4, 1))
    );
    assert_eq!(witness.schedule().fire[&EventId::new(3, 0)], 0);
}

struct OneLabel(Label);
impl Program for OneLabel {
    fn num_threads(&self) -> usize {
        1
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        vec![if traces[0].is_empty() {
            ThreadNext::Next(self.0.clone())
        } else {
            ThreadNext::Finished
        }]
    }
}

#[test]
fn unsupported_effects_and_empty_nondet_are_unknown() {
    for label in [
        Label::recv_nb(Pred::any()),
        Label::send(Model::P2p, 0, "x"),
        Label::error("stop"),
        Label::Nondet {
            set: Vec::<Val>::new().into(),
        },
    ] {
        assert!(matches!(
            check_completion(
                &ExecutionGraph::new(),
                &OneLabel(label),
                LookaheadBudget::default()
            ),
            CompletionCheck::Unknown(_)
        ));
    }
}

#[test]
fn a_maximal_blocked_graph_is_a_witness_not_an_unknown_future() {
    let outcome = check_completion(
        &ExecutionGraph::new(),
        &OneLabel(Label::recv(Pred::any())),
        LookaheadBudget::default(),
    );
    let CompletionCheck::Witness(witness) = outcome else {
        panic!("maximal deadlock is terminal");
    };
    assert_eq!(witness.terminal_graph().all_events().len(), 0);
}

struct DataChoice {
    always_early: bool,
}

impl Program for DataChoice {
    fn num_threads(&self) -> usize {
        3
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..3)
            .map(|tid| {
                let events = match tid {
                    0 => vec![send(1, "slow", 10)],
                    1 => vec![victim()],
                    2 if self.always_early || traces[2].first() == Some(&Some("a".into())) => {
                        vec![Label::nondet(["a", "b"]), send(1, "early", 1)]
                    }
                    2 => vec![Label::nondet(["a", "b"]), send(1, "other", 1)],
                    _ => unreachable!(),
                };
                events
                    .get(traces[tid].len())
                    .cloned()
                    .map(ThreadNext::Next)
                    .unwrap_or(ThreadNext::Finished)
            })
            .collect()
    }
}

#[test]
fn nondeterministic_guards_cover_all_values_without_merging_their_effects() {
    let mut graph = ExecutionGraph::new();
    let slow = graph.add_event(0, send(1, "slow", 10));
    let receive = graph.add_event(1, victim());
    graph.set_rf(receive, Some(slow));
    let CompletionCheck::Impossible(certificate) = check_completion(
        &graph,
        &DataChoice { always_early: true },
        LookaheadBudget::default(),
    ) else {
        panic!("both data choices emit an early competitor");
    };
    assert_eq!(
        certificate.coverage()[0].alternatives(),
        &[
            ChoiceGuard::Nondet {
                event: EventId::new(2, 0),
                value: "a".into()
            },
            ChoiceGuard::Nondet {
                event: EventId::new(2, 0),
                value: "b".into()
            },
        ]
    );
    let CompletionCheck::Witness(witness) = check_completion(
        &graph,
        &DataChoice {
            always_early: false,
        },
        LookaheadBudget::default(),
    ) else {
        panic!("the second choice has no competing early effect");
    };
    assert_eq!(
        witness.terminal_graph().nd_value(EventId::new(2, 0)),
        Some(&Val::from("b"))
    );
}
