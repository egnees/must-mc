//! Independent regressions for the two certificate layers. The reference run retains
//! untimed MUST's canonical construction and checks time only at terminals.
//!
//! These examples distinguish forward impossibility from construction-subtree
//! impossibility: an infeasible commitment may still have a valid backward revisit.

mod common;

use common::{assert_no_duplicates, permutations, SeqProgram};
use must::{
    check, explore, traces_of, Config, EventId, ExecutionCollector, ExecutionGraph, Label, Model,
    Observer, Pred, Program, ThreadNext, TimeCertificateEvent, TimeCertificateOutcome, Val, Window,
};
use std::sync::Mutex;

fn send(dst: usize, value: &str, lo: u64, hi: u64) -> Label {
    Label::send_within(Model::Asyn, dst, value, Window::new(lo, hi))
}

fn fixed_send(dst: usize, value: &str, delay: u64) -> Label {
    send(dst, value, delay, delay)
}

fn victim() -> Label {
    Label::recv(Pred::new("early|slow", |v| matches!(v, "early" | "slow")))
}

fn relay() -> Label {
    Label::recv(Pred::new("red|blue", |v| matches!(v, "red" | "blue")))
}

/// Both variants have the same frontier and the same exact union of possible
/// future labels. Only their relation between received values and sends differs.
#[derive(Clone)]
struct Fork {
    always_early: bool,
}

impl Fork {
    fn suffix(&self, tid: usize, trace: &[Option<Val>]) -> Vec<Label> {
        let events = match tid {
            0 => vec![fixed_send(1, "slow", 10)],
            1 => vec![victim()],
            2 => vec![fixed_send(3, "red", 1), fixed_send(3, "blue", 1)],
            3 => {
                if trace.is_empty() {
                    return vec![
                        relay(),
                        fixed_send(1, "early", 0),
                        fixed_send(1, "other", 0),
                    ];
                }
                if trace[0] == Some("red".into()) {
                    vec![relay(), fixed_send(1, "early", 0)]
                } else if self.always_early {
                    vec![
                        relay(),
                        fixed_send(1, "other", 0),
                        fixed_send(1, "early", 0),
                    ]
                } else {
                    vec![relay(), fixed_send(1, "other", 0)]
                }
            }
            _ => unreachable!(),
        };
        events[trace.len().min(events.len())..].to_vec()
    }
}

impl Program for Fork {
    fn num_threads(&self) -> usize {
        4
    }

    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..4)
            .map(|tid| {
                self.suffix(tid, &traces[tid])
                    .first()
                    .cloned()
                    .map_or(ThreadNext::Finished, ThreadNext::Next)
            })
            .collect()
    }

    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        Some(self.suffix(tid, trace))
    }
}

fn fork_prefix() -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let source = g.add_event(0, fixed_send(1, "slow", 10));
    let receive = g.add_event(1, victim());
    g.set_rf(receive, Some(source));
    g.add_event(2, fixed_send(3, "red", 1));
    g.add_event(2, fixed_send(3, "blue", 1));
    g
}

fn fork_terminal(program: &Fork, source_idx: usize) -> ExecutionGraph {
    let mut g = fork_prefix();
    let receive = g.add_event(3, relay());
    g.set_rf(receive, Some(EventId::new(2, source_idx)));
    loop {
        let next = program.next(&traces_of(&g, 4));
        match &next[3] {
            ThreadNext::Next(label) => {
                g.add_event(3, label.clone());
            }
            ThreadNext::Finished => break,
        }
    }
    g
}

/// A current T2 run really visits the r <- slow target with T2 unexpanded.
/// Whatever q receives, its zero-time suffix sends early at time 1 and prevents
/// r from consuming slow at time 10. This covers exact, value-independent futures.
#[derive(Clone)]
struct ReachableFork {
    value_independent: bool,
}

impl ReachableFork {
    fn events(&self, tid: usize, trace: &[Option<Val>]) -> Vec<Label> {
        match tid {
            0 => vec![Label::recv(Pred::new("a|early|slow", |v| {
                matches!(v, "a" | "early" | "slow")
            }))],
            1 => vec![send(0, "a", 0, 20)],
            2 if !self.value_independent && trace.first() == Some(&Some("blue".into())) => vec![
                relay(),
                fixed_send(0, "other", 0),
                fixed_send(0, "early", 0),
            ],
            2 => vec![relay(), fixed_send(0, "early", 0)],
            3 => vec![fixed_send(2, "red", 1), fixed_send(2, "blue", 1)],
            4 => vec![Label::recv(Pred::eq("x")), fixed_send(0, "slow", 0)],
            5 => vec![fixed_send(4, "x", 10)],
            _ => unreachable!(),
        }
    }
}

impl Program for ReachableFork {
    fn num_threads(&self) -> usize {
        6
    }

    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..6)
            .map(|tid| {
                self.events(tid, &traces[tid])
                    .get(traces[tid].len())
                    .cloned()
                    .map_or(ThreadNext::Finished, ThreadNext::Next)
            })
            .collect()
    }

    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        if tid == 2 && trace.is_empty() {
            let mut labels = vec![relay(), fixed_send(0, "early", 0)];
            if !self.value_independent {
                labels.push(fixed_send(0, "other", 0));
            }
            return Some(labels);
        }
        let events = self.events(tid, trace);
        Some(events[trace.len().min(events.len())..].to_vec())
    }
}

#[derive(Default)]
struct VisitAudit {
    // (all visits, barren visits, slow-target visits, barren slow-target visits)
    counts: Mutex<[usize; 4]>,
    certificates: Mutex<Vec<TimeCertificateEvent>>,
}

impl Observer for VisitAudit {
    fn on_time_certificate(&self, _g: &ExecutionGraph, event: &TimeCertificateEvent) {
        self.certificates.lock().unwrap().push(*event);
    }

    fn on_visit_exit(&self, g: &ExecutionGraph, produced: bool) {
        let mut counts = self.counts.lock().unwrap();
        counts[0] += 1;
        counts[1] += usize::from(!produced);
        if g.reads_from(EventId::new(0, 0)) == Some(EventId::new(4, 1)) && g.thread_len(2) == 0 {
            counts[2] += 1;
            counts[3] += usize::from(!produced);
        }
    }
}

fn keys<P: Program + Clone + Sync>(program: &P, config: Config) -> Vec<String> {
    let collector = ExecutionCollector::new();
    explore(|| program.clone(), &collector, config);
    assert_no_duplicates(&collector, "certified-time regression");
    let mut keys = collector.terminal_keys();
    keys.sort();
    keys
}

fn reference<P: Program + Clone + Sync>(program: &P, priorities: &[usize]) -> Vec<String> {
    let config = Config::default()
        .collect_errors()
        .with_priorities(priorities.to_vec());
    let filtered = keys(program, config.clone().with_time_filter());
    let zombie = keys(program, config.with_time_zombie());
    assert_eq!(filtered, zombie, "independent reference policies disagree");
    filtered
}

/// Original untimed canonicity sometimes has to retain an infeasible prefix in
/// order to discover the backward revisit yielding fast_a and fast_b together.
fn revisit_escape_program() -> SeqProgram {
    SeqProgram::new(vec![
        vec![fixed_send(1, "slow_a", 5), fixed_send(1, "fast_a", 1)],
        vec![Label::recv(Pred::new("a-family", |v| v.ends_with("_a")))],
        vec![fixed_send(3, "slow_b", 5)],
        vec![Label::recv(Pred::new("b-family", |v| v.ends_with("_b")))],
        vec![fixed_send(3, "fast_b", 1)],
    ])
}

#[test]
fn same_future_alphabet_does_not_imply_same_completion() {
    let bad = Fork { always_early: true };
    let good = Fork {
        always_early: false,
    };
    let g = fork_prefix();
    let traces = traces_of(&g, 4);
    assert_eq!(bad.next(&traces), good.next(&traces));
    for (tid, trace) in traces.iter().enumerate() {
        assert_eq!(
            bad.possible_future(tid, trace),
            good.possible_future(tid, trace)
        );
    }
    assert!(check(&g).is_feasible());
    for (program, expected) in [(&bad, [false, false]), (&good, [false, true])] {
        for (source_idx, feasible) in expected.into_iter().enumerate() {
            let terminal = fork_terminal(program, source_idx);
            assert_eq!(check(&terminal).is_feasible(), feasible);
            assert_eq!(
                common::time_feasible_ref(&terminal, &mut 100),
                Some(feasible),
                "fixed-delay independent reference"
            );
        }
    }
}

#[test]
fn reference_preserves_escape_from_infeasible_commitments() {
    let program = revisit_escape_program();
    let expected = reference(&program, &[0, 2, 3, 1, 4]);
    assert_eq!(expected.len(), 1);
    for priorities in permutations(5) {
        assert_eq!(reference(&program, &priorities), expected);
    }
}

fn certified_config(priorities: &[usize], priority_policy: bool) -> Config {
    let mut config = Config::default()
        .collect_errors()
        .with_priorities(priorities.to_vec());
    if priority_policy {
        config = config.with_time_filter();
    }
    config
        .with_certified_time()
        .with_certified_time_budget(10_000, 100)
}

#[test]
fn future_certificates_distinguish_common_and_conditional_effects() {
    use must::time::future::{check_completion, CompletionCheck, LookaheadBudget};

    let g = fork_prefix();
    let budget = LookaheadBudget {
        max_states: 10_000,
        max_added_events: 100,
    };
    assert!(matches!(
        check_completion(&g, &Fork { always_early: true }, budget),
        CompletionCheck::Impossible(_)
    ));
    assert!(matches!(
        check_completion(
            &g,
            &Fork {
                always_early: false
            },
            budget
        ),
        CompletionCheck::Witness(_)
    ));
}

#[test]
fn exhausted_future_budget_is_unknown() {
    use must::time::future::{check_completion, CompletionCheck, LookaheadBudget};

    let program = Fork { always_early: true };
    for budget in [
        LookaheadBudget {
            max_states: 0,
            max_added_events: 100,
        },
        LookaheadBudget {
            max_states: 100,
            max_added_events: 0,
        },
    ] {
        assert!(matches!(
            check_completion(&fork_prefix(), &program, budget),
            CompletionCheck::Unknown(_)
        ));
    }
}

#[test]
fn certified_fork_keys_match_both_references_without_duplicates() {
    for always_early in [false, true] {
        let program = Fork { always_early };
        let expected = reference(&program, &[0, 1, 2, 3]);
        assert_eq!(expected.len(), 2, "one valid graph per relay source");
        for priorities in permutations(4) {
            assert_eq!(reference(&program, &priorities), expected);
            for priority_policy in [false, true] {
                let actual = keys(&program, certified_config(&priorities, priority_policy));
                assert_eq!(
                    actual, expected,
                    "order={priorities:?}, priority={priority_policy}"
                );
            }
        }
    }
}

#[test]
fn certified_pruning_preserves_canonical_revisit_escape() {
    let program = revisit_escape_program();
    let expected = reference(&program, &[0, 2, 3, 1, 4]);
    assert_eq!(expected.len(), 1);
    for priorities in permutations(5) {
        for priority_policy in [false, true] {
            let actual = keys(&program, certified_config(&priorities, priority_policy));
            assert_eq!(
                actual, expected,
                "order={priorities:?}, priority={priority_policy}"
            );
        }
    }
}

#[test]
fn exhausted_certificate_budget_preserves_terminal_keys() {
    let programs = [revisit_escape_program(), common::blocked_no_match()];
    for program in programs {
        let priorities = (0..program.num_threads()).collect::<Vec<_>>();
        let expected = reference(&program, &priorities);
        for priority_policy in [false, true] {
            let config =
                certified_config(&priorities, priority_policy).with_certified_time_budget(0, 0);
            assert_eq!(keys(&program, config), expected);
        }
    }
}

#[test]
fn certified_pruning_reduces_reachable_barren_visits() {
    for value_independent in [false, true] {
        let program = ReachableFork { value_independent };
        let priorities = [0, 1, 2, 3, 4, 5];
        let baseline = (ExecutionCollector::new(), VisitAudit::default());
        explore(
            || program.clone(),
            &baseline,
            Config::default().collect_errors().with_time_zombie(),
        );
        let certified = (ExecutionCollector::new(), VisitAudit::default());
        explore(
            || program.clone(),
            &certified,
            certified_config(&priorities, false),
        );
        let baseline_counts = *baseline.1.counts.lock().unwrap();
        let certified_counts = *certified.1.counts.lock().unwrap();
        assert!(
            baseline_counts[2] > 0,
            "reference must reach the slow target"
        );
        assert_eq!(baseline_counts[2], baseline_counts[3]);
        assert!(certified_counts[2] <= baseline_counts[2]);
        assert_eq!(
            certified_counts[2], certified_counts[3],
            "examined pruning boundaries are counted and must remain barren"
        );
        assert!(
            certified_counts[0] < baseline_counts[0],
            "main Visit count must decrease"
        );
        assert!(
            certified_counts[1] < baseline_counts[1],
            "barren Visit count must decrease"
        );
        let certificates = certified.1.certificates.lock().unwrap();
        assert!(certificates.iter().any(|event| {
            event.outcome == TimeCertificateOutcome::Pruned && event.ownership_states > 0
        }));
        println!(
            "value_independent={value_independent}: main Visits {} -> {}, barren {} -> {}, proof states {} + {}",
            baseline_counts[0], certified_counts[0], baseline_counts[1], certified_counts[1],
            certificates.iter().map(|event| event.completion_states).sum::<usize>(),
            certificates.iter().map(|event| event.ownership_states).sum::<usize>()
        );
        let mut actual = certified.0.terminal_keys();
        actual.sort();
        let expected = reference(&program, &priorities);
        assert_eq!(expected.len(), 4);
        assert_eq!(actual, expected);
        assert_no_duplicates(&certified.0, "reachable certified-time regression");
    }
}

/// No `possible_future` implementation: a certificate must not interpret an
/// absent summary as an empty future, or assume the first nondeterministic value.
#[derive(Clone)]
struct NondetFuture;

impl Program for NondetFuture {
    fn num_threads(&self) -> usize {
        2
    }

    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        let first = match traces[0].len() {
            0 => ThreadNext::Next(Label::nondet(["early", "skip"])),
            1 if traces[0][0] == Some("early".into()) => {
                ThreadNext::Next(fixed_send(1, "early", 0))
            }
            1 => ThreadNext::Next(fixed_send(0, "other", 0)),
            _ => ThreadNext::Finished,
        };
        let second = match traces[1].len() {
            0 => ThreadNext::Next(fixed_send(1, "slow", 10)),
            1 => ThreadNext::Next(victim()),
            _ => ThreadNext::Finished,
        };
        vec![first, second]
    }
}

#[test]
fn missing_future_summary_keeps_nondeterministic_completions() {
    let program = NondetFuture;
    for priorities in permutations(2) {
        let expected = reference(&program, &priorities);
        assert_eq!(expected.len(), 2);
        for priority_policy in [false, true] {
            assert_eq!(
                keys(&program, certified_config(&priorities, priority_policy)),
                expected
            );
        }
    }
}

#[test]
fn escaping_revisit_is_reported_as_unresolved_ownership() {
    let program = revisit_escape_program();
    let priorities = [0, 2, 3, 1, 4];
    let observers = (ExecutionCollector::new(), VisitAudit::default());
    explore(
        || program.clone(),
        &observers,
        certified_config(&priorities, true),
    );
    let events = observers.1.certificates.lock().unwrap();
    assert!(
        events.iter().any(|event| {
            event.outcome == TimeCertificateOutcome::OwnershipUnknown
                && event.revisit_candidates > 0
                && event.ownership_states > 0
        }),
        "semantic impossibility must not discharge an admitted backward revisit"
    );
    assert_eq!(observers.0.terminal_count(), 1);
    assert_no_duplicates(&observers.0, "ownership-refusal regression");
}

#[test]
fn parallel_certified_runs_preserve_keys() {
    let program = ReachableFork {
        value_independent: false,
    };
    let priorities = [0, 1, 2, 3, 4, 5];
    let expected = reference(&program, &priorities);
    for workers in [2, 3] {
        for priority_policy in [false, true] {
            assert_eq!(
                keys(
                    &program,
                    certified_config(&priorities, priority_policy).with_threads(workers)
                ),
                expected
            );
        }
    }
}

#[test]
#[should_panic(expected = "certified timing")]
fn certified_pruning_rejects_t2_canonical_rules() {
    let collector = ExecutionCollector::new();
    explore(
        revisit_escape_program,
        &collector,
        Config::default()
            .collect_errors()
            .with_time_predicate()
            .with_certified_time(),
    );
}

#[test]
fn generated_bounded_programs_preserve_terminal_keys() {
    // Fixed arithmetic seed: failures reproduce without external generators or
    // environmental randomness. Each program has 3/4 processes, <=3 events each,
    // and at most one two-valued nondeterministic event.
    fn draw(seed: &mut u64, bound: usize) -> usize {
        *seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        ((*seed >> 32) as usize) % bound
    }

    fn generated_send(seed: &mut u64, dst: usize) -> Label {
        let payload = ["a", "b"][draw(seed, 2)];
        let lo = draw(seed, 5) as u64;
        let hi = lo + draw(seed, 4) as u64;
        send(dst, payload, lo, hi)
    }

    let mut seed = 0xc3_71_f1_ed_20_26_u64;
    let mut saw_blocked = false;
    let mut saw_full = false;
    let mut compared_runs = 0;
    for case in 0..40 {
        let n = 3 + case % 2;
        let mut threads = Vec::new();
        for tid in 0..n {
            let len = 1 + draw(&mut seed, 3);
            let mut events = Vec::new();
            for index in 0..len {
                let event = if tid == 0 && index == 0 {
                    Label::recv(Pred::any())
                } else if index == 0 && (tid == 1 || tid == 2) {
                    // Supply competing sends to a shared mailbox.
                    generated_send(&mut seed, 0)
                } else if tid == 0 && index == 1 && case % 5 == 0 {
                    Label::nondet(["left", "right"])
                } else {
                    match draw(&mut seed, 5) {
                        0 => Label::recv(Pred::eq("a")),
                        1 => Label::recv(Pred::any()),
                        _ => {
                            let dst = draw(&mut seed, n);
                            generated_send(&mut seed, dst)
                        }
                    }
                };
                events.push(event);
            }
            threads.push(events);
        }
        if case % 7 == 0 {
            // A message with this value never exists, so these cases exercise
            // maximal blocked graphs as valid terminals, rather than rejecting them.
            threads[n - 1] = vec![Label::recv(Pred::eq("never-sent"))];
        }
        let program = SeqProgram::new(threads);
        let base_order = (0..n).collect::<Vec<_>>();
        let mut rotated = base_order.clone();
        rotated.rotate_left(1);
        let orders = [base_order.clone(), (0..n).rev().collect(), rotated];
        let collector = ExecutionCollector::new();
        explore(
            || program.clone(),
            &collector,
            Config::default().collect_errors().with_time_filter(),
        );
        saw_blocked |= collector.blocked_count() > 0;
        saw_full |= collector.full_count() > 0;
        assert_no_duplicates(&collector, "generated reference");
        let mut expected = collector.terminal_keys();
        expected.sort();
        assert!(
            !expected.is_empty(),
            "generated case {case} has no maximal terminal"
        );
        for priorities in orders {
            assert_eq!(
                reference(&program, &priorities),
                expected,
                "reference: generated case {case}, order={priorities:?}, program={:?}",
                program.threads
            );
            for priority_policy in [false, true] {
                let actual = keys(&program, certified_config(&priorities, priority_policy));
                assert_eq!(
                    actual, expected,
                    "generated case {case}, order={priorities:?}, priority={priority_policy}, program={:?}",
                    program.threads
                );
                compared_runs += 1;
            }
        }
    }
    assert!(
        saw_blocked && saw_full,
        "corpus must exercise both terminal kinds"
    );
    assert_eq!(compared_runs, 240);
}
