//! Independent checks of the structural arguments used by mailbox timing pruning.
//! The corpus enumerates RF assignments directly, without MUST's canonical rules.

use std::collections::BTreeSet;

use must::{consistent, EventId, ExecutionGraph, Label, Model, Pred, Window};

const MODELS: [Model; 3] = [Model::Asyn, Model::P2p, Model::Mbox];

fn graph(
    code: usize,
    earlier: usize,
    held: usize,
    selective: bool,
) -> (ExecutionGraph, EventId, EventId) {
    let mut digits = code;
    let models: Vec<_> = (0..5)
        .map(|_| {
            let model = MODELS[digits % MODELS.len()];
            digits /= MODELS.len();
            model
        })
        .collect();
    let send = |model, dst, value| Label::send_within(model, dst, value, Window::new(0, 2));
    let mut graph = ExecutionGraph::new();
    let m = graph.add_event(0, send(Model::Asyn, 0, "m"));
    let pred = if selective {
        Pred::eq(["a", "b", "c"][earlier])
    } else {
        Pred::any()
    };
    let q = graph.add_event(0, Label::recv_poll_timed(pred, Window::new(0, 2)));
    let x = graph.add_event(0, send(models[0], 2, "x"));
    let r = graph.add_event(0, Label::recv(Pred::any()));

    // The timeout is a real time-advancing empty receive. It is retained whenever
    // any later event of this process is retained in a closed restriction.
    graph.add_event(1, Label::recv_timeout_timed(Pred::any(), Window::new(1, 1)));
    let a = graph.add_event(1, send(models[1], 0, "a"));
    let bridge = graph.add_event(1, Label::recv(Pred::eq("wake")));
    let b = graph.add_event(1, send(models[2], 0, "b"));

    let wake = graph.add_event(2, send(models[3], 1, "wake"));
    let relay = graph.add_event(2, Label::recv(Pred::eq("x")));
    let c = graph.add_event(2, send(models[4], 0, "c"));
    let sources = [a, b, c];
    graph.set_rf(q, Some(sources[earlier]));
    graph.set_rf(r, Some(sources[held]));
    graph.set_rf(bridge, Some(wake));
    graph.set_rf(relay, Some(x));
    (graph, m, r)
}

#[test]
fn ancestral_asyn_replacement_preserves_mixed_mailbox_consistency() {
    let mut checked = 0;
    let mut with_mbox = 0;
    for code in 0..MODELS.len().pow(5) {
        for earlier in 0..3 {
            for held in 0..3 {
                if earlier == held {
                    continue;
                }
                for selective in [false, true] {
                    let (mut graph, m, r) = graph(code, earlier, held, selective);
                    if !consistent(&graph) {
                        continue;
                    }
                    assert!(graph.porf_reaches(m, r));
                    assert!(graph.matches(m, r));
                    assert!(!graph.is_read(m));
                    assert_eq!(
                        r.idx + 1,
                        graph.thread_len(r.tid),
                        "r ends its process in Previous"
                    );
                    with_mbox += usize::from(
                        graph
                            .iter_sends()
                            .any(|s| graph.send_model(s) == Some(Model::Mbox)),
                    );
                    let original = graph.canonical_key();
                    graph.set_rf(r, Some(m));
                    assert!(
                        consistent(&graph),
                        "ancestral Asyn replacement introduced inconsistency:\n{original}"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert!(
        checked > 500 && with_mbox > 300,
        "checked={checked}, with_mbox={with_mbox}"
    );
    eprintln!("ancestral Asyn transfer: {checked} consistent graphs, {with_mbox} containing Mbox");
}

#[test]
fn feasible_mailbox_graphs_preserve_all_closed_process_prefixes() {
    let mut checked_graphs = 0;
    let mut checked_restrictions = 0;
    // A fixed stride bounds solver work while spanning all five transport choices.
    for code in (0..MODELS.len().pow(5)).step_by(17) {
        for (earlier, held) in [(0, 1), (1, 2)] {
            let (graph, _, _) = graph(code, earlier, held, false);
            if !consistent(&graph) {
                continue;
            }
            let must::time::TimedVerdict::Feasible(schedule) = must::time::check_mailbox(&graph)
            else {
                continue;
            };
            assert!(must::time::verify_mailbox_schedule(&graph, &schedule));
            checked_graphs += 1;
            for l0 in 0..=graph.thread_len(0) {
                for l1 in 0..=graph.thread_len(1) {
                    for l2 in 0..=graph.thread_len(2) {
                        let lengths = [l0, l1, l2];
                        let keep: BTreeSet<_> = graph
                            .iter_events()
                            .filter(|e| e.idx < lengths[e.tid])
                            .collect();
                        if keep
                            .iter()
                            .any(|&e| graph.reads_from(e).is_some_and(|s| !keep.contains(&s)))
                        {
                            continue;
                        }
                        let restricted = graph.restrict(&keep);
                        assert!(consistent(&restricted));
                        let must::time::TimedVerdict::Feasible(witness) =
                            must::time::check_mailbox(&restricted)
                        else {
                            panic!("feasible graph lost feasibility under RF/PO closed restriction: code={code}, lengths={lengths:?}\n{}", graph.canonical_key());
                        };
                        assert!(must::time::verify_mailbox_schedule(&restricted, &witness));
                        checked_restrictions += 1;
                    }
                }
            }
        }
    }
    assert!(
        checked_graphs >= 15 && checked_restrictions > 500,
        "graphs={checked_graphs}, restrictions={checked_restrictions}"
    );
    eprintln!("mailbox restriction: {checked_restrictions} closed prefixes of {checked_graphs} feasible graphs");
}
