//! Observer and render tests: these check that the observers see the run and that the
//! text renderer produces sensible, non-empty, panic-free output.

use must::observer::{RecordingObserver, StepKind};
use must::render::{render_execution, render_graph, render_log};
use must::{
    explore, Config, CountingObserver, ExecutionCollector, ExecutionKind, Model, NullObserver,
    System,
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
