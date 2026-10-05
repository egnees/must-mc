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
