//! Timed receive annotations survive coroutine replay, graph identity and rendering.

use std::collections::BTreeSet;

use must::event::{Label, Pred, ReceiveTiming, Val};
use must::graph::ExecutionGraph;
use must::{Model, Program, System, ThreadNext, Window};

fn next_label(system: &System, trace: &[Option<Val>]) -> Label {
    match system.next_thread(0, trace) {
        ThreadNext::Next(label) => label,
        ThreadNext::Finished => panic!("expected a next event"),
    }
}

#[test]
fn existing_receives_keep_the_abstract_contract() {
    let mut system = System::new();
    system.add(|ctx| async move {
        let _ = ctx.recv(|_| true).await;
        let _ = ctx.recv_timeout(|_| true).await;
    });
    let blocking = next_label(&system, &[]);
    assert_eq!(blocking.receive_timing(), Some(ReceiveTiming::Abstract));
    assert_eq!(blocking.blocking(), Some(true));
    let nonblocking = next_label(&system, &[Some("m".into())]);
    assert_eq!(nonblocking.receive_timing(), Some(ReceiveTiming::Abstract));
    assert_eq!(nonblocking.blocking(), Some(false));
    assert!(!blocking.is_timed_recv());
    assert!(!nonblocking.is_timed_recv());
}

#[test]
fn timed_receive_metadata_and_outcomes_survive_replay() {
    let mut system = System::new();
    system.add(|ctx| async move {
        let first = ctx
            .recv_timeout_timed(|m| m == "ready", Window::new(2, 3))
            .await;
        let poll_window = if first.is_some() {
            Window::new(0, 0)
        } else {
            Window::new(4, 6)
        };
        let second = ctx.recv_poll_timed(|m| m == "reply", poll_window).await;
        ctx.send(
            0,
            second.unwrap_or_else(|| "empty".to_string()),
            Model::Asyn,
        );
    });
    let first = next_label(&system, &[]);
    assert_eq!(
        first.receive_timing(),
        Some(ReceiveTiming::Timeout(Window::new(2, 3)))
    );
    assert_eq!(first.blocking(), Some(false));
    assert!(first.pred().unwrap().test("ready"));
    assert!(!first.pred().unwrap().test("reply"));
    assert_eq!(
        first,
        next_label(&system, &[]),
        "repeat replay preserves the label"
    );

    for (outcome, window) in [
        (None, Window::new(4, 6)),
        (Some("ready".into()), Window::new(0, 0)),
    ] {
        let second = next_label(&system, &[outcome]);
        assert_eq!(second.receive_timing(), Some(ReceiveTiming::Poll(window)));
        assert_eq!(second.blocking(), Some(false));
        assert!(second.pred().unwrap().test("reply"));
        assert!(!second.pred().unwrap().test("ready"));
        assert_eq!(next_label(&system, &[outcome, None]).val(), Some("empty"));
        assert_eq!(
            next_label(&system, &[outcome, Some("reply".into())]).val(),
            Some("reply")
        );
    }
}

#[test]
fn receive_budget_counts_timed_empty_returns() {
    let mut system = System::new();
    let tid = system.add(|ctx| async move {
        loop {
            let _ = ctx.recv_timeout_timed(|_| true, Window::new(2, 2)).await;
            let _ = ctx.recv_poll_timed(|_| true, Window::new(3, 3)).await;
        }
    });
    system.set_max_recvs(tid, 2);
    assert!(next_label(&system, &[None]).is_timed_recv());
    assert!(system.next_thread(tid, &[None, None]).is_finished());
}

#[test]
fn receive_mode_and_window_participate_in_graph_identity() {
    let labels = [
        Label::recv_nb(Pred::any()),
        Label::recv_timeout_timed(Pred::any(), Window::ASAP),
        Label::recv_poll_timed(Pred::any(), Window::ASAP),
        Label::recv_timeout_timed(Pred::any(), Window::new(2, 3)),
        Label::recv_timeout_timed(Pred::any(), Window::new(2, 4)),
        Label::recv_poll_timed(Pred::any(), Window::new(2, 3)),
    ];
    let mut keys = BTreeSet::new();
    for (index, label) in labels.into_iter().enumerate() {
        let mut graph = ExecutionGraph::new();
        let receive = graph.add_event(0, label.clone());
        graph.set_rf(receive, None);
        if index == 0 {
            assert_eq!(graph.canonical_key(), "T0: Rnb[4:true]\nrf: ⟨0,0⟩<-⊥\nnd:");
        } else {
            assert!(
                label.is_timed_recv(),
                "ASAP is still an explicit receive contract"
            );
        }
        assert!(keys.insert(graph.canonical_key()));
        let restricted = graph.restrict(&[receive].into_iter().collect());
        assert_eq!(restricted.label(receive), &label);
        assert_eq!(restricted.canonical_key(), graph.canonical_key());
    }
}

#[test]
fn text_rendering_distinguishes_timeout_and_poll_windows() {
    let mut graph = ExecutionGraph::new();
    graph.add_event(
        0,
        Label::recv_timeout_timed(Pred::any(), Window::new(5, 10)),
    );
    graph.add_event(0, Label::recv_poll_timed(Pred::any(), Window::at_least(3)));
    let rendered = must::render::render_graph(&graph);
    assert!(rendered.contains("Rnb[true] timeout[5,10]"));
    assert!(rendered.contains("Rnb[true] poll[3,∞]"));
}
