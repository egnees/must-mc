use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use must::{
    explore, Config, EventCountingObserver, Execution, ExecutionGraph, ExecutionKind, Model,
    Observer, System, TraceLabel,
};

type Snapshot = (String, Vec<TraceLabel>, ExecutionKind);

#[derive(Default)]
struct LegacyRecorder(Mutex<Vec<Snapshot>>);

impl LegacyRecorder {
    fn record(&self, graph: &ExecutionGraph, labels: &[TraceLabel], kind: ExecutionKind) {
        self.0
            .lock()
            .unwrap()
            .push((graph.canonical_key(), labels.to_vec(), kind));
    }

    fn snapshots(&self) -> Vec<Snapshot> {
        let mut snapshots = self.0.lock().unwrap().clone();
        snapshots.sort_by(|a, b| a.0.cmp(&b.0));
        snapshots
    }
}

impl Observer for LegacyRecorder {
    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        self.record(exec.graph(), exec.labels(), kind);
    }
}

#[derive(Default)]
struct ViewRecorder {
    records: LegacyRecorder,
    views: AtomicUsize,
    owned: AtomicUsize,
    stop: bool,
}

impl Observer for ViewRecorder {
    fn accepts_execution_view(&self) -> bool {
        true
    }

    fn on_execution_view(
        &self,
        graph: &ExecutionGraph,
        labels: &[TraceLabel],
        kind: ExecutionKind,
    ) {
        self.views.fetch_add(1, Ordering::Relaxed);
        self.records.record(graph, labels, kind);
    }

    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        self.owned.fetch_add(1, Ordering::Relaxed);
        self.records.on_execution(exec, kind);
    }

    fn should_stop(&self) -> bool {
        self.stop && self.views.load(Ordering::Relaxed) > 0
    }
}

fn outcomes() -> System {
    let mut system = System::new();
    system.add(|ctx| async move {
        ctx.insert_label("before choice");
        let choice = ctx.nondet(["full", "blocked", "error"]).await;
        ctx.insert_label(choice.clone());
        ctx.insert_label("same position");
        if choice == "full" {
            ctx.send(0, "message", Model::Asyn);
            let value = ctx.recv_any().await;
            ctx.insert_label(value);
        } else if choice == "blocked" {
            ctx.recv_any().await;
        } else {
            ctx.assert_that(false, "expected error");
        }
    });
    system
}

fn choices() -> System {
    let mut system = System::new();
    system.add(|ctx| async move {
        for _ in 0..10 {
            let value = ctx.nondet(["0", "1"]).await;
            ctx.insert_label(value);
        }
    });
    system
}

#[test]
fn borrowed_and_owned_callbacks_preserve_terminals_and_labels() {
    for threads in [1, 12] {
        let config = Config::default().collect_errors().with_threads(threads);
        let legacy = LegacyRecorder::default();
        let view = ViewRecorder::default();
        explore(outcomes, &legacy, config.clone());
        explore(outcomes, &view, config);
        assert_eq!(view.records.snapshots(), legacy.snapshots());
        assert_eq!(view.views.load(Ordering::Relaxed), 3);
        assert_eq!(view.owned.load(Ordering::Relaxed), 0);
        assert!(view
            .records
            .snapshots()
            .iter()
            .all(|(_, labels, _)| !labels.is_empty()));
    }
}

#[test]
fn mixed_and_nested_tuples_preserve_legacy_callbacks() {
    for threads in [1, 12] {
        let observer = (
            (LegacyRecorder::default(), LegacyRecorder::default()),
            (EventCountingObserver::new(), ViewRecorder::default()),
        );
        explore(
            outcomes,
            &observer,
            Config::default().collect_errors().with_threads(threads),
        );
        let ((first, second), (counts, view)) = &observer;
        let expected = view.records.snapshots();
        assert_eq!(first.snapshots(), expected);
        assert_eq!(second.snapshots(), expected);
        assert_eq!(counts.full(), 1);
        assert_eq!(counts.blocked(), 1);
        assert_eq!(counts.errors(), 1);
    }
}

#[test]
fn borrowed_callbacks_preserve_stop_requests_and_execution_caps() {
    for threads in [1, 12] {
        for stop in [false, true] {
            let observer = ViewRecorder {
                stop,
                ..ViewRecorder::default()
            };
            let config = Config {
                threads,
                max_executions: (!stop).then_some(3),
                ..Config::default()
            };
            explore(choices, &observer, config);
            let count = observer.views.load(Ordering::Relaxed);
            assert!((1..1024).contains(&count));
            if threads == 1 {
                assert_eq!(count, if stop { 1 } else { 3 });
            }
            assert_eq!(observer.owned.load(Ordering::Relaxed), 0);
        }
    }
}

#[test]
fn timed_regimes_keep_owned_callbacks() {
    for config in [
        Config::default().collect_errors().with_time_filter(),
        Config::default().collect_errors().with_time_zombie(),
        Config::default().collect_errors().with_time_predicate(),
    ] {
        let observer = ViewRecorder::default();
        explore(outcomes, &observer, config);
        assert_eq!(observer.views.load(Ordering::Relaxed), 0);
        assert_eq!(observer.owned.load(Ordering::Relaxed), 3);
    }
}

#[test]
fn view_opt_in_does_not_bypass_unsupported_timed_model_guard() {
    let observer = ViewRecorder::default();
    let result = std::panic::catch_unwind(|| {
        explore(
            || {
                let mut system = System::new();
                system.add(|ctx| async move {
                    ctx.send_within(0, "unsupported", Model::Cd, must::Window::new(1, 2));
                });
                system
            },
            &observer,
            Config::default().collect_errors().with_time_filter(),
        );
    });
    assert!(result.is_err());
    assert_eq!(observer.views.load(Ordering::Relaxed), 0);
    assert_eq!(observer.owned.load(Ordering::Relaxed), 0);
}
