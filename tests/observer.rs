//! Observer and render tests: these check that the observers see the run and that the
//! text renderer produces sensible, non-empty, panic-free output.

use std::sync::atomic::{AtomicUsize, Ordering};

use must::observer::{RecordingObserver, StepKind};
use must::render::{render_execution, render_graph, render_log};
use must::{
    explore, Config, CountingObserver, Execution, ExecutionCollector, ExecutionGraph,
    ExecutionKind, Model, NullObserver, Observer, System,
};

/// Build s+s+r as a real system (`T0: send(2,1) || T1: send(2,2) || T2: recv()`).
fn ssr() -> System {
    let mut sys = System::new();
    sys.add(|c| async move {
        c.send(2, "1", Model::P2p);
    });
    sys.add(|c| async move {
        c.send(2, "2", Model::P2p);
    });
    sys.add(|c| async move {
        let _ = c.recv(|_| true).await;
    });
    sys
}

#[test]
fn null_observer_is_a_noop() {
    // A NullObserver ignores every callback; the run still completes without panicking.
    explore(ssr, &NullObserver, Config::default());
}

#[test]
fn counting_observer_tallies_the_run() {
    let obs = CountingObserver::new();
    explore(ssr, &obs, Config::default());

    assert_eq!(obs.full(), 2);
    assert_eq!(obs.terminal(), obs.full() + obs.blocked());
    // Adding three sends + one receive (per branch) and trying rf sources must have
    // produced events and rf choices.
    assert!(obs.events_added() > 0, "some events were added");
    assert!(obs.rf_choices() > 0, "some rf sources were tried");
    // A blocking receive reading nothing is inconsistent and must be dropped at least once.
    assert!(
        obs.inconsistent() > 0,
        "the ⊥ branch of the receive is dropped"
    );
}

#[test]
fn event_counter_matches_full_instrumentation_for_parallel_outcomes_and_cuts() {
    use must::{EventCountingObserver, Label, Pred, Program, ThreadNext, Val};
    #[derive(Clone)]
    struct Script(Vec<Vec<Label>>);
    impl Program for Script {
        fn num_threads(&self) -> usize {
            self.0.len()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.0
                .iter()
                .zip(traces)
                .map(|(events, trace)| {
                    events
                        .get(trace.len())
                        .cloned()
                        .map_or(ThreadNext::Finished, ThreadNext::Next)
                })
                .collect()
        }
    }
    for model in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
        for (outcome, receives) in [
            ("full", vec![Label::recv(Pred::any())]),
            ("blocked", vec![Label::recv(Pred::any()); 4]),
            (
                "error",
                vec![Label::recv(Pred::any()), Label::error("failure")],
            ),
            ("cut", vec![Label::recv(Pred::any())]),
        ] {
            let program = Script(vec![
                vec![Label::send(model, 2, "a"), Label::send(model, 2, "b")],
                vec![Label::send(model, 2, "c")],
                receives,
            ]);
            for threads in [1, 4] {
                for shards in [0, 1, 2, 7] {
                    let counters = (
                        EventCountingObserver::with_shards(shards),
                        CountingObserver::with_shards(shards),
                    );
                    let mut config = Config {
                        threads,
                        ..Config::default().collect_errors()
                    };
                    if outcome == "cut" {
                        config.max_sends = Some(1);
                    }
                    explore(|| program.clone(), &counters, config);
                    assert_eq!(counters.0.events_added(), counters.1.events_added());
                    assert_eq!(counters.0.full(), counters.1.full());
                    assert_eq!(counters.0.blocked(), counters.1.blocked());
                    assert_eq!(counters.0.errors(), counters.1.errors());
                    assert_eq!(counters.0.terminal(), counters.1.terminal());
                    assert!(counters.0.events_added() > 0);
                    match outcome {
                        "full" => assert!(counters.0.full() > 0),
                        "blocked" => assert!(counters.0.blocked() > 0),
                        "error" => assert!(counters.0.errors() > 0),
                        "cut" => assert!(counters.1.send_limit_hits() > 0),
                        _ => unreachable!(),
                    }
                }
            }
        }
    }
}

#[test]
fn event_counter_atomic_shards_preserve_colliding_thread_updates() {
    let counter = must::EventCountingObserver::with_shards(0);
    std::thread::scope(|scope| {
        for _ in 0..8 {
            let counter = &counter;
            scope.spawn(move || {
                let exec = dummy_exec();
                for _ in 0..1000 {
                    counter.on_event_added(exec.graph(), must::EventId::new(0, 0));
                    counter.on_execution(&exec, ExecutionKind::Full);
                    counter.on_execution(&exec, ExecutionKind::Blocked);
                    counter.on_execution(&exec, ExecutionKind::Error);
                    counter.on_execution_filtered(&exec, ExecutionKind::Full);
                }
            });
        }
    });
    assert_eq!(counter.events_added(), 8000);
    assert_eq!(counter.full(), 8000);
    assert_eq!(counter.blocked(), 8000);
    assert_eq!(counter.errors(), 8000);
    assert_eq!(counter.terminal(), 16000);
}

#[test]
fn conservative_tuple_partners_preserve_immediate_added_events_and_graphs() {
    struct Probe<'a> {
        counter: &'a must::EventCountingObserver,
        callbacks: AtomicUsize,
    }
    impl Observer for Probe<'_> {
        fn on_event_added(&self, graph: &ExecutionGraph, event: must::EventId) {
            assert!(graph.contains(event));
            let callbacks = self.callbacks.fetch_add(1, Ordering::Relaxed) + 1;
            assert_eq!(self.counter.events_added(), callbacks);
        }
    }
    for buffered in [false, true] {
        let mut counter = must::EventCountingObserver::default();
        if buffered {
            counter = counter.with_buffered_events();
        }
        let probe = Probe {
            counter: &counter,
            callbacks: AtomicUsize::new(0),
        };
        let observers = (&counter, probe);
        // Use a wrapper so the tuple owns an Observer rather than relying on a
        // blanket Observer implementation for references.
        struct CounterRef<'a>(&'a must::EventCountingObserver);
        impl Observer for CounterRef<'_> {
            fn allows_buffered_events(&self) -> bool {
                self.0.allows_buffered_events()
            }
            fn on_event_added(&self, g: &ExecutionGraph, e: must::EventId) {
                self.0.on_event_added(g, e);
            }
            fn on_execution(&self, e: &Execution, k: ExecutionKind) {
                self.0.on_execution(e, k);
            }
        }
        let observers = (CounterRef(observers.0), observers.1);
        assert!(!observers.allows_buffered_events());
        explore(ssr, &observers, Config::default());
        assert!(counter.events_added() > 0);
        assert_eq!(
            counter.events_added(),
            observers.1.callbacks.load(Ordering::Relaxed)
        );
    }
}

#[test]
fn buffered_added_events_match_immediate_totals_for_complete_and_stopped_runs() {
    fn make(model: Model) -> System {
        let mut system = System::new();
        system.add(move |c| async move {
            c.send(2, "a", model);
            c.send(2, "b", model);
        });
        system.add(move |c| async move {
            c.send(2, "c", model);
        });
        system.add(|c| async move {
            let value = c.recv_any().await;
            if value == "a" {
                let _ = c.recv(|v| v == "missing").await;
            }
            if value == "b" {
                c.assert_that(false, "error branch");
            }
        });
        system
    }
    for model in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
        for threads in [1, 4] {
            let mut configs = vec![
                Config::default().collect_errors().with_threads(threads),
                Config::default()
                    .collect_errors()
                    .with_threads(threads)
                    .with_max_sends(2),
            ];
            if threads == 1 {
                configs.extend([
                    Config::default(),
                    Config {
                        max_executions: Some(1),
                        ..Config::default().collect_errors()
                    },
                    Config::default().with_stop_on_terminal_error(),
                ]);
            }
            for config in configs {
                let immediate = must::EventCountingObserver::with_shards(1);
                let buffered = must::EventCountingObserver::with_shards(1).with_buffered_events();
                assert!(!immediate.allows_buffered_events());
                assert!(buffered.allows_buffered_events());
                explore(|| make(model), &immediate, config.clone());
                explore(|| make(model), &buffered, config.clone());
                assert_eq!(
                    buffered.events_added(),
                    immediate.events_added(),
                    "model={model:?}, config={config:?}"
                );
                assert_eq!(buffered.full(), immediate.full());
                assert_eq!(buffered.blocked(), immediate.blocked());
                assert_eq!(buffered.errors(), immediate.errors());
            }
        }
    }
}

#[test]
fn buffered_added_events_flush_on_unwind_and_share_shards_across_concurrent_runs() {
    struct PanicOnReceive;
    impl Observer for PanicOnReceive {
        fn allows_buffered_events(&self) -> bool {
            true
        }
        fn on_rf_choice(&self, _g: &ExecutionGraph, _r: must::EventId, _s: Option<must::EventId>) {
            panic!("intentional observer panic");
        }
    }
    for buffered in [false, true] {
        let mut counter = must::EventCountingObserver::with_shards(1);
        if buffered {
            counter = counter.with_buffered_events();
        }
        let observers = (counter, PanicOnReceive);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            explore(ssr, &observers, Config::default())
        }));
        assert!(result.is_err());
        assert_eq!(
            observers.0.events_added(),
            3,
            "two sends and the receive precede the panic"
        );
    }
    let reference = must::EventCountingObserver::default();
    explore(ssr, &reference, Config::default().with_threads(4));
    let shared = must::EventCountingObserver::with_shards(1).with_buffered_events();
    std::thread::scope(|scope| {
        for _ in 0..8 {
            let shared = &shared;
            scope.spawn(move || explore(ssr, shared, Config::default().with_threads(4)));
        }
    });
    assert_eq!(shared.events_added(), 8 * reference.events_added());
    assert_eq!(shared.full(), 8 * reference.full());
    assert_eq!(shared.blocked(), 8 * reference.blocked());
    assert_eq!(shared.errors(), 8 * reference.errors());
}

#[test]
fn parallel_observer_unwind_stops_idle_workers_and_flushes_added_events() {
    use std::sync::mpsc;
    use std::time::Duration;
    struct Panics {
        at_execution: bool,
    }
    impl Observer for Panics {
        fn allows_buffered_events(&self) -> bool {
            self.at_execution
        }
        fn on_event_added(&self, _graph: &ExecutionGraph, _event: must::EventId) {
            assert!(self.at_execution, "intentional event-added observer panic");
        }
        fn on_execution(&self, _execution: &Execution, _kind: ExecutionKind) {
            assert!(!self.at_execution, "intentional execution observer panic");
        }
    }
    fn one_path() -> System {
        let mut system = System::new();
        system.add(|c| async move {
            c.send(0, "one", Model::Asyn);
            c.send(0, "two", Model::Asyn);
            c.assert_that(false, "terminal error");
        });
        system
    }
    for at_execution in [false, true] {
        let (sender, receiver) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let observers = (
                must::EventCountingObserver::with_shards(1).with_buffered_events(),
                Panics { at_execution },
            );
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                explore(one_path, &observers, Config::default().with_threads(4));
            }));
            sender
                .send((
                    result.is_err(),
                    observers.0.events_added(),
                    observers.0.errors(),
                ))
                .unwrap();
        });
        let (panicked, events, errors) = receiver.recv_timeout(Duration::from_secs(5)).expect(
            "parallel unwind must wake idle workers rather than waiting for unfinished work",
        );
        worker.join().unwrap();
        assert!(panicked);
        // This program has one construction path and no donatable siblings. Only
        // its active worker adds anything; all waiting workers contribute zero.
        assert_eq!(events, if at_execution { 3 } else { 1 });
        assert_eq!(errors, usize::from(at_execution));
    }
}

#[test]
fn recording_observer_logs_steps_and_executions() {
    let rec = RecordingObserver::new();
    explore(ssr, &rec, Config::default());

    assert!(!rec.is_empty(), "the log is non-empty");
    let steps = rec.steps();
    let executions = steps
        .iter()
        .filter(|s| {
            matches!(
                s.kind,
                StepKind::Execution {
                    kind: ExecutionKind::Full
                }
            )
        })
        .count();
    assert_eq!(executions, 2, "two Full execution steps recorded");
    let events_added = steps
        .iter()
        .filter(|s| matches!(s.kind, StepKind::EventAdded { .. }))
        .count();
    assert!(events_added > 0);
}

#[test]
fn observers_compose_as_a_tuple() {
    let both = (CountingObserver::new(), RecordingObserver::new());
    explore(ssr, &both, Config::default());
    assert_eq!(both.0.full(), 2);
    assert!(!both.1.is_empty());
}

#[test]
fn render_execution_is_sensible() {
    let col = ExecutionCollector::new();
    explore(ssr, &col, Config::default());
    for exec in col.full() {
        let text = render_execution(&exec);
        assert!(!text.is_empty());
        assert!(text.contains("T0"), "renders thread columns: {text}");
        assert!(text.contains("rf:"), "renders rf edges: {text}");
        assert!(
            text.contains("pending sends:"),
            "renders pending sends: {text}"
        );
    }
}

// -- on_execution_filtered (A3a: the seam the eager time filter will drive in A3b) ----
//
// The explorer does not call this callback yet (that arrives with `Config::time_filter`
// in A3b), so these tests drive it directly on hand-built executions.

/// A throwaway execution over an empty graph, enough to exercise the callbacks.
fn dummy_exec() -> Execution {
    Execution::new(ExecutionGraph::new())
}

/// An observer that overrides nothing, to prove the new trait method has a working
/// default (no-op) body: an existing implementation compiles and does not panic.
struct SilentObserver;
impl Observer for SilentObserver {}

/// Counts `on_execution_filtered` calls, per kind -- used to check tuple forwarding.
#[derive(Default)]
struct FilteredCounter {
    full: AtomicUsize,
    blocked: AtomicUsize,
    errors: AtomicUsize,
}
impl Observer for FilteredCounter {
    fn on_execution_filtered(&self, _exec: &Execution, kind: ExecutionKind) {
        match kind {
            ExecutionKind::Full => &self.full,
            ExecutionKind::Blocked => &self.blocked,
            ExecutionKind::Error => &self.errors,
        }
        .fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn on_execution_filtered_default_is_a_noop() {
    // The default trait body must not panic and must leave observers that ignore it (like
    // NullObserver) untouched -- existing implementations keep working unchanged.
    NullObserver.on_execution_filtered(&dummy_exec(), ExecutionKind::Full);
    SilentObserver.on_execution_filtered(&dummy_exec(), ExecutionKind::Blocked);
}

#[test]
fn tuple_forwards_on_execution_filtered_to_both() {
    // Risk #3 of the plan: the tuple observer must fan the new callback out to *both*
    // halves, or the default no-op would silently swallow it on the untouched side.
    let both = (FilteredCounter::default(), FilteredCounter::default());
    both.on_execution_filtered(&dummy_exec(), ExecutionKind::Full);
    both.on_execution_filtered(&dummy_exec(), ExecutionKind::Error);
    assert_eq!(both.0.full.load(Ordering::Relaxed), 1);
    assert_eq!(both.1.full.load(Ordering::Relaxed), 1);
    assert_eq!(both.0.errors.load(Ordering::Relaxed), 1);
    assert_eq!(both.1.errors.load(Ordering::Relaxed), 1);
}

#[test]
fn counting_observer_accumulates_filtered() {
    let obs = CountingObserver::new();
    obs.on_execution_filtered(&dummy_exec(), ExecutionKind::Full);
    obs.on_execution_filtered(&dummy_exec(), ExecutionKind::Full);
    obs.on_execution_filtered(&dummy_exec(), ExecutionKind::Blocked);
    obs.on_execution_filtered(&dummy_exec(), ExecutionKind::Error);

    assert_eq!(obs.filtered_full(), 2);
    assert_eq!(obs.filtered_blocked(), 1);
    assert_eq!(obs.filtered_errors(), 1);
    assert_eq!(obs.filtered(), 4);
    // Filtered terminals stay out of the ordinary tallies (they are not reported).
    assert_eq!(obs.full(), 0);
    assert_eq!(obs.blocked(), 0);
    assert_eq!(obs.errors(), 0);
    assert_eq!(obs.terminal(), 0);
}

#[test]
fn execution_collector_accumulates_filtered() {
    let col = ExecutionCollector::new();
    col.on_execution_filtered(&dummy_exec(), ExecutionKind::Full);
    col.on_execution_filtered(&dummy_exec(), ExecutionKind::Blocked);

    assert_eq!(col.filtered_count(), 2);
    assert_eq!(col.filtered().len(), 2);
    // Two empty graphs share a canonical key; the accessor sorts, so it is deterministic.
    let keys = col.filtered_keys();
    assert_eq!(keys.len(), 2);
    assert!(keys.windows(2).all(|w| w[0] <= w[1]), "keys are sorted");
    // The ordinary buckets are untouched.
    assert_eq!(col.full_count(), 0);
    assert_eq!(col.terminal_count(), 0);
}

#[test]
fn recording_observer_logs_filtered_step() {
    let rec = RecordingObserver::new();
    rec.on_execution_filtered(&dummy_exec(), ExecutionKind::Blocked);
    let steps = rec.steps();
    assert_eq!(steps.len(), 1);
    assert!(matches!(
        steps[0].kind,
        StepKind::ExecutionFiltered {
            kind: ExecutionKind::Blocked
        }
    ));
}

#[test]
fn render_graph_handles_empty_graph() {
    let text = render_graph(&must::ExecutionGraph::new());
    assert!(!text.is_empty());
}

#[test]
fn render_log_is_non_empty_and_panic_free() {
    let rec = RecordingObserver::new();
    explore(ssr, &rec, Config::default());
    let text = render_log(&rec);
    assert!(!text.is_empty());
    // No byte-slice of `text`: the graph render contains multi-byte glyphs, so a slice
    // like `&text[..80]` could split a UTF-8 boundary on the failure path.
    assert!(text.contains("step 0"), "render_log should number frames");
}
