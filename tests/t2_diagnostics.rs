//! A false research hypothesis must not interrupt enumeration of valid terminals.

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};

use common::SeqProgram;
use must::{
    explore, Config, CountingObserver, EventId, ExecutionCollector, ExecutionGraph, Label, Model,
    Observer, Pred, Val, Window,
};

#[derive(Default)]
struct Diagnostics {
    candidates: AtomicUsize,
    rejected_arms: AtomicUsize,
    false_held: AtomicUsize,
}

impl Observer for Diagnostics {
    fn on_revisit_candidate(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _target: &ExecutionGraph,
    ) {
        self.candidates.fetch_add(1, Ordering::Relaxed);
    }

    fn on_revisit_arm_rejected(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _target: &ExecutionGraph,
        _event: EventId,
    ) {
        self.rejected_arms.fetch_add(1, Ordering::Relaxed);
    }

    fn on_held_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _value: Val,
        _revisiting: EventId,
        _rev_label: &Label,
        verdict: bool,
    ) {
        if !verdict {
            self.false_held.fetch_add(1, Ordering::Relaxed);
        }
    }
}

fn program() -> SeqProgram {
    let send =
        |dst, value, lo, hi| Label::send_within(Model::Asyn, dst, value, Window::new(lo, hi));
    SeqProgram::new(vec![
        vec![
            Label::nondet(["a", "b"]),
            send(0, "a", 1, 4),
            send(0, "b", 4, 4),
            Label::recv(Pred::any()),
            Label::nondet(["a", "b"]),
        ],
        vec![
            send(1, "g", 1, 1),
            Label::recv(Pred::eq("g")),
            send(0, "early", 1, 1),
        ],
    ])
}

#[test]
fn false_held_viability_is_observable_without_losing_terminals() {
    let p = program();
    let reference = ExecutionCollector::new();
    explore(
        || p.clone(),
        &reference,
        Config::default().collect_errors().with_time_filter(),
    );
    let mut wanted = reference.full_keys();
    wanted.sort();
    assert_eq!(wanted.len(), 8);
    assert!(wanted.windows(2).all(|pair| pair[0] != pair[1]));

    for workers in [1, 2] {
        // Composition exercises forwarding of the new diagnostic callbacks too.
        let observed = (
            Diagnostics::default(),
            (CountingObserver::new(), ExecutionCollector::new()),
        );
        explore(
            || p.clone(),
            &observed,
            Config::default()
                .collect_errors()
                .with_time_predicate()
                .with_threads(workers),
        );
        // Parallel callbacks can arrive in any order. Sorting retains duplicate
        // records, so equality still requires exactly the eight distinct terminals.
        let mut actual = observed.1 .1.full_keys();
        actual.sort();
        assert_eq!(actual, wanted, "workers={workers}");
        assert_eq!(observed.1 .0.full(), 8, "duplicate reports");
        assert_eq!(observed.1 .0.blocked(), 0);
        assert_eq!(observed.1 .0.errors(), 0);
        assert!(observed.0.candidates.load(Ordering::Relaxed) > 0);
        assert!(observed.0.rejected_arms.load(Ordering::Relaxed) > 0);
        if cfg!(debug_assertions) {
            assert!(observed.0.false_held.load(Ordering::Relaxed) > 0);
        } else {
            assert_eq!(observed.0.false_held.load(Ordering::Relaxed), 0);
        }
    }
}
