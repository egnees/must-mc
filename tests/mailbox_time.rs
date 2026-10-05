//! Regressions for the direct mailbox contract; legacy timing tests remain separate.
use must::event::{EventId, Label, Model, Pred, Window};
use must::time::{
    check_mailbox, earliest_mailbox_times, verify_mailbox_schedule, Action, TimedVerdict,
};
use must::ExecutionGraph;

fn send(model: Model, dst: usize, value: &str, time: u64) -> Label {
    Label::send_within(model, dst, value, Window::new(time, time))
}
fn timeout(value: &str, lo: u64, hi: u64) -> Label {
    Label::recv_timeout_timed(pred(value), Window::new(lo, hi))
}
fn poll(value: &str, lo: u64, hi: u64) -> Label {
    Label::recv_poll_timed(pred(value), Window::new(lo, hi))
}
fn pred(value: &str) -> Pred {
    if value == "*" {
        Pred::any()
    } else {
        Pred::eq(value)
    }
}
/// One `rf` edge: `((tid, idx)` of the receive, its source `(tid, idx)` or `None` for ⊥`)`.
type ReadEdge = ((usize, usize), Option<(usize, usize)>);

fn graph(threads: Vec<Vec<Label>>, reads: &[ReadEdge]) -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    for (tid, thread) in threads.into_iter().enumerate() {
        for label in thread {
            g.add_event(tid, label);
        }
    }
    for &(r, s) in reads {
        g.set_rf(EventId::new(r.0, r.1), s.map(|s| EventId::new(s.0, s.1)));
    }
    g
}
fn feasible(g: &ExecutionGraph) -> bool {
    match check_mailbox(g) {
        TimedVerdict::Feasible(schedule) => {
            assert!(verify_mailbox_schedule(g, &schedule));
            true
        }
        TimedVerdict::Infeasible(_) => false,
    }
}

#[test]
fn direct_windows_reject_fifo_inversion_even_without_receives() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        let g = graph(
            vec![
                vec![send(model, 1, "a", 10), send(model, 1, "b", 1)],
                vec![],
            ],
            &[],
        );
        assert_eq!(feasible(&g), model == Model::Asyn, "{model:?}");
    }
}

#[test]
fn fifo_overlapping_intervals_can_adjust_delivery() {
    for model in [Model::P2p, Model::Mbox] {
        let g = graph(
            vec![
                vec![
                    Label::send_within(model, 1, "a", Window::new(5, 10)),
                    Label::send_within(model, 1, "b", Window::new(2, 8)),
                ],
                vec![],
            ],
            &[],
        );
        assert!(feasible(&g));
    }
}

#[test]
fn fifo_does_not_include_asyn_or_other_destinations() {
    for model in [Model::P2p, Model::Mbox] {
        let g = graph(
            vec![
                vec![
                    send(model, 1, "a", 10),
                    send(Model::Asyn, 1, "b", 1),
                    send(model, 2, "c", 1),
                ],
                vec![],
                vec![],
            ],
            &[],
        );
        assert!(feasible(&g));
    }
}

#[test]
fn fifo_tie_cannot_hide_previously_queued_message() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        let g = graph(
            vec![
                vec![send(model, 1, "m", 1), send(model, 1, "n", 1)],
                vec![Label::recv(pred("n")), timeout("m", 0, 0)],
            ],
            &[((1, 0), Some((0, 1))), ((1, 1), None)],
        );
        assert_eq!(feasible(&g), model == Model::Asyn, "{model:?}");
    }
}

#[test]
fn zero_time_empty_can_enable_later_send_at_same_time() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        let g = graph(
            vec![vec![timeout("*", 0, 0), send(model, 0, "x", 0)]],
            &[((0, 0), None)],
        );
        assert!(feasible(&g));
    }
}

#[test]
fn selective_receives_can_consume_reverse_delivery_order() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        let g = graph(
            vec![
                vec![send(model, 1, "a", 1), send(model, 1, "b", 2)],
                vec![Label::recv(pred("b")), Label::recv(pred("a"))],
            ],
            &[((1, 0), Some((0, 1))), ((1, 1), Some((0, 0)))],
        );
        assert!(feasible(&g));
    }
}

#[test]
fn timeout_success_may_precede_lower_bound_but_poll_may_not() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        for polling in [false, true] {
            let recv = if polling {
                poll("*", 5, 10)
            } else {
                timeout("*", 5, 10)
            };
            let g = graph(
                vec![
                    vec![send(model, 1, "x", 2)],
                    vec![recv, send(model, 2, "reply", 1)],
                    vec![timeout("*", 4, 4)],
                ],
                &[((1, 0), Some((0, 0))), ((2, 0), Some((1, 1)))],
            );
            assert_eq!(feasible(&g), !polling, "{model:?}, polling={polling}");
        }
    }
}

#[test]
fn empty_returns_advance_all_later_clocks_and_lower_bounds() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        let g = graph(
            vec![
                vec![timeout("*", 2, 2), poll("*", 3, 3), send(model, 1, "x", 1)],
                vec![],
            ],
            &[((0, 0), None), ((0, 1), None)],
        );
        let TimedVerdict::Feasible(schedule) = check_mailbox(&g) else {
            panic!("{model:?}")
        };
        assert_eq!(schedule.fire[&EventId::new(0, 0)], 2);
        assert_eq!(schedule.fire[&EventId::new(0, 1)], 5);
        assert_eq!(schedule.arr[&EventId::new(0, 2)], 6);
        assert!(verify_mailbox_schedule(&g, &schedule));
        let earliest = earliest_mailbox_times(&g).unwrap();
        assert_eq!(earliest.fire_lb(EventId::new(0, 1)), Some(5));
        assert_eq!(earliest.avail_lb(EventId::new(0, 2)), Some(6));
    }
}

#[test]
fn empty_outcome_accounts_for_later_consumed_message() {
    let g = graph(
        vec![
            vec![send(Model::Asyn, 1, "x", 1)],
            vec![poll("*", 2, 2), Label::recv(pred("*"))],
        ],
        &[((1, 0), None), ((1, 1), Some((0, 0)))],
    );
    assert!(!feasible(&g));
}

#[test]
fn only_timed_empty_receives_still_require_solver() {
    let g = graph(vec![vec![timeout("*", 5, 5)]], &[((0, 0), None)]);
    assert!(must::time::assert_supported_models(&g));
    let TimedVerdict::Feasible(schedule) = must::time::check(&g) else {
        panic!()
    };
    assert_eq!(schedule.fire[&EventId::new(0, 0)], 5);
}

#[test]
fn mbox_fifo_follows_actual_send_order_across_senders() {
    // T1 cannot send before time 2. Asyn/P2p may overtake T0's time-zero send;
    // Mbox must keep actual send order for this destination.
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        let g = graph(
            vec![
                vec![send(model, 2, "a", 10)],
                vec![poll("absent", 2, 2), send(model, 2, "b", 1)],
                vec![],
            ],
            &[((1, 0), None)],
        );
        assert_eq!(feasible(&g), model != Model::Mbox, "{model:?}");
    }
}

#[test]
fn mbox_queued_selection_respects_send_order() {
    let g = graph(
        vec![
            vec![send(Model::Mbox, 2, "a", 1)],
            vec![poll("absent", 2, 2), send(Model::Mbox, 2, "b", 1)],
            vec![poll("absent", 5, 5), Label::recv(pred("*"))],
        ],
        &[((1, 0), None), ((2, 0), None), ((2, 1), Some((1, 1)))],
    );
    // Untimed Mbox could order sender 1 first; the physical invocation times forbid it.
    assert!(must::consistency::consistent(&g));
    assert!(!feasible(&g));
}

#[test]
fn mbox_independent_concurrent_send_order_is_chosen_inside_verifier() {
    let g = graph(
        vec![
            vec![send(Model::Mbox, 2, "a", 10)],
            vec![send(Model::Mbox, 2, "b", 1)],
            vec![Label::recv(pred("*"))],
        ],
        &[((2, 0), Some((1, 0)))],
    );
    assert!(feasible(&g));
}

#[test]
fn schedule_checker_rejects_invalid_equal_time_order_and_delivery() {
    let g = graph(
        vec![vec![timeout("*", 0, 0), send(Model::Asyn, 0, "x", 0)]],
        &[((0, 0), None)],
    );
    let TimedVerdict::Feasible(mut s) = check_mailbox(&g) else {
        panic!()
    };
    assert!(verify_mailbox_schedule(&g, &s));
    let delivery = s
        .actions
        .iter()
        .position(|s| s.action == Action::Deliver(EventId::new(0, 1)))
        .unwrap();
    s.actions.swap(0, delivery);
    assert!(!verify_mailbox_schedule(&g, &s));
    s.actions.swap(0, delivery);
    s.arr.insert(EventId::new(0, 1), 1);
    assert!(!verify_mailbox_schedule(&g, &s));
}

#[test]
#[should_panic(expected = "requires an explicit Timeout or Poll")]
fn abstract_nb_does_not_silently_become_time_transparent() {
    check_mailbox(&graph(
        vec![vec![Label::recv_nb(pred("*"))]],
        &[((0, 0), None)],
    ));
}

#[test]
#[should_panic(expected = "does not support Cd")]
fn cd_is_explicitly_unsupported_even_with_default_windows() {
    check_mailbox(&graph(vec![vec![Label::send(Model::Cd, 0, "x")]], &[]));
}

#[test]
fn original_abstract_nb_keeps_legacy_semantics() {
    let g = graph(vec![vec![Label::recv_nb(pred("*"))]], &[((0, 0), None)]);
    assert!(must::time::check(&g).is_feasible());
}
