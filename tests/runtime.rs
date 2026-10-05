//! Runtime replay tests: these exercise the coroutine replay and the `Program`
//! boundary with hand-written traces only - no execution graph, no consistency,
//! no explorer.

use must::event::{Label, Val};
use must::{Model, Program, System, ThreadNext, Window};

/// Convenience: a `None` trace entry stands for a send/error event (its `G.val` is nothing).
const S: Option<Val> = None;

fn v(x: &str) -> Option<Val> {
    Some(x.into())
}

/// Assert a `ThreadNext` is a send with the given destination and value.
fn assert_send(n: &ThreadNext, dst: usize, val: &str) {
    match n {
        ThreadNext::Next(Label::Send {
            dst: d, val: vv, ..
        }) => {
            assert_eq!(*d, dst, "send dst");
            assert_eq!(must::intern::resolve(*vv), val, "send val");
        }
        other => panic!("expected Send({dst},{val}), got {other:?}"),
    }
}

fn assert_recv(n: &ThreadNext) {
    match n {
        ThreadNext::Next(Label::Recv { blocking, .. }) => {
            assert!(*blocking, "phase-A recv is blocking")
        }
        other => panic!("expected Recv, got {other:?}"),
    }
}

/// Assert a `ThreadNext` is a **non-blocking** receive (`recv_timeout`).
fn assert_recv_nb(n: &ThreadNext) {
    match n {
        ThreadNext::Next(Label::Recv { blocking, .. }) => {
            assert!(!*blocking, "expected a non-blocking receive")
        }
        other => panic!("expected non-blocking Recv, got {other:?}"),
    }
}

fn assert_error(n: &ThreadNext, msg: &str) {
    match n {
        ThreadNext::Next(Label::Error { msg: m }) => assert_eq!(&**m, msg),
        other => panic!("expected Error({msg}), got {other:?}"),
    }
}

fn assert_finished(n: &ThreadNext) {
    assert!(n.is_finished(), "expected Finished, got {n:?}");
}

// -- Single-thread building blocks ------------------------------------------------

/// Parking on recv: an empty trace makes the first event of a receiver a `Recv`.
#[test]
fn parks_on_recv() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let _ = ctx.recv(|_| true).await;
    });
    let out = sys.next(&[vec![]]);
    assert_recv(&out[0]);
}

/// A process that only sends finishes after its sends are enumerated.
#[test]
fn finishes_after_sends() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        ctx.send(1, "a", Model::P2p);
        ctx.send(1, "b", Model::P2p);
    });
    assert_send(&sys.next(&[vec![]])[0], 1, "a");
    assert_send(&sys.next(&[vec![S]])[0], 1, "b");
    assert_finished(&sys.next(&[vec![S, S]])[0]);
}

/// Several sends are buffered before a recv and enumerated one-by-one, in order.
#[test]
fn buffers_sends_before_recv() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        ctx.send(2, "m1", Model::P2p);
        ctx.send(2, "m2", Model::P2p);
        let _ = ctx.recv(|_| true).await;
    });
    assert_send(&sys.next(&[vec![]])[0], 2, "m1");
    assert_send(&sys.next(&[vec![S]])[0], 2, "m2");
    assert_recv(&sys.next(&[vec![S, S]])[0]);
    // After the recv resolves, the body ends.
    assert_finished(&sys.next(&[vec![S, S, v("x")]])[0]);
}

/// send;recv;send;recv - all four events enumerated in the right order.
#[test]
fn send_recv_send_recv() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        ctx.send(1, "a", Model::P2p);
        let x = ctx.recv(|_| true).await;
        ctx.send(1, format!("b{x}"), Model::P2p); // value depends on received value
        let _ = ctx.recv(|_| true).await;
    });
    assert_send(&sys.next(&[vec![]])[0], 1, "a");
    assert_recv(&sys.next(&[vec![S]])[0]);
    // The second send's payload reflects the value the first recv returned ("1").
    assert_send(&sys.next(&[vec![S, v("1")]])[0], 1, "b1");
    assert_recv(&sys.next(&[vec![S, v("1"), S]])[0]);
    assert_finished(&sys.next(&[vec![S, v("1"), S, v("9")]])[0]);
}

/// Sending to oneself is allowed.
#[test]
fn send_to_self() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let me = ctx.tid();
        ctx.send(me, "self", Model::Mbox);
    });
    match &sys.next(&[vec![]])[0] {
        ThreadNext::Next(Label::Send {
            dst, val, model, ..
        }) => {
            assert_eq!(*dst, 0);
            assert_eq!(must::intern::resolve(*val), "self");
            assert_eq!(*model, Model::Mbox);
        }
        other => panic!("expected self-send, got {other:?}"),
    }
}

/// A plain `send` carries the default (untimed) window; `send_within` carries the given
/// one. The window rides through replay into the emitted `Label::Send`.
#[test]
fn send_within_emits_window() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        ctx.send(1, "plain", Model::P2p);
        ctx.send_within(1, "timed", Model::P2p, Window::new(10, 20));
    });
    match &sys.next(&[vec![]])[0] {
        ThreadNext::Next(l @ Label::Send { .. }) => {
            assert_eq!(l.window(), Some(Window::ASAP), "plain send is untimed");
        }
        other => panic!("expected Send, got {other:?}"),
    }
    match &sys.next(&[vec![S]])[0] {
        ThreadNext::Next(l @ Label::Send { .. }) => {
            assert_eq!(l.window(), Some(Window::new(10, 20)), "send_within window");
        }
        other => panic!("expected Send, got {other:?}"),
    }
}

/// A violated assertion emits `Label::Error` as the next event; a holding one is a
/// no-op (pure control flow).
#[test]
fn assert_that_emits_error() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        ctx.assert_that(true, "ok"); // no event
        ctx.assert_that(false, "boom"); // error event
        ctx.send(1, "unreached", Model::P2p);
    });
    assert_error(&sys.next(&[vec![]])[0], "boom");
}

/// The predicate carried by a parked `Recv` really tests messages.
#[test]
fn recv_predicate_is_carried() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let _ = ctx.recv(|x| x == "2").await;
    });
    match &sys.next(&[vec![]])[0] {
        ThreadNext::Next(Label::Recv { pred, .. }) => {
            assert!(pred.test("2"));
            assert!(!pred.test("1"));
        }
        other => panic!("expected Recv, got {other:?}"),
    }
}

/// A blocking receive that read nothing terminates the thread.
#[test]
fn blocking_recv_of_bottom_finishes() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let _ = ctx.recv(|_| true).await;
        ctx.send(1, "after", Model::P2p);
    });
    // The single receive read nothing (its trace entry is None): the thread blocks.
    assert_finished(&sys.next(&[vec![S]])[0]);
}

// -- Non-blocking receive (recv_timeout) ------------------------------------------

/// Parking on `recv_timeout`: an empty trace makes the first event a *non-blocking*
/// receive (`Label::recv_nb`), distinct from a blocking `recv`.
#[test]
fn parks_on_recv_timeout() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let _ = ctx.recv_timeout(|_| true).await;
    });
    assert_recv_nb(&sys.next(&[vec![]])[0]);
}

/// The crux of non-blocking receives: unlike a blocking receive, one that read nothing
/// (trace entry `None`) does **not** block - it resolves to `None` and the thread runs
/// on. Here the body's next event after reading nothing is a distinct send, proving
/// control flow continued past the timeout.
#[test]
fn recv_timeout_of_bottom_continues() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let x = ctx.recv_timeout(|_| true).await;
        let tag = if x.is_none() { "timeout" } else { "got" };
        ctx.send(1, tag, Model::P2p);
    });
    // The receive read nothing: the thread continues and its next event is send("timeout").
    assert_send(&sys.next(&[vec![S]])[0], 1, "timeout");
}

/// A non-blocking receive that read a value resolves to `Some(v)` and the thread runs on.
#[test]
fn recv_timeout_of_value_continues() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let x = ctx.recv_timeout(|_| true).await;
        let tag = if x.is_none() { "timeout" } else { "got" };
        ctx.send(1, tag, Model::P2p);
    });
    // The receive read "m": the thread continues and its next event is send("got").
    assert_send(&sys.next(&[vec![v("m")]])[0], 1, "got");
    // The received value is available to the body (would be usable as a payload, etc.).
    assert_finished(&sys.next(&[vec![v("m"), S]])[0]);
}

/// Mixed blocking and non-blocking receives in one body: the runtime distinguishes them
/// *structurally* (by which API the body called), not by the trace entry's shape. Both
/// `Some` and `None` are legal at either position.
#[test]
fn mixed_blocking_and_nonblocking_in_one_body() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        let _ = ctx.recv_timeout(|_| true).await; // event 0: non-blocking
        let _ = ctx.recv(|_| true).await; // event 1: blocking
        ctx.send(1, "done", Model::P2p); // event 2
    });
    // Empty trace: first event is the non-blocking receive.
    assert_recv_nb(&sys.next(&[vec![]])[0]);
    // First receive resolved (to nothing here): next event is the blocking receive.
    assert_recv(&sys.next(&[vec![S]])[0]);
    // Both resolved to values: next is the send.
    assert_send(&sys.next(&[vec![v("a"), v("b")]])[0], 1, "done");
    // The blocking receive reading nothing still blocks the thread even after a nb receive.
    assert_finished(&sys.next(&[vec![v("a"), S]])[0]);
}

// -- Determinism ------------------------------------------------------------------

#[test]
fn replay_is_deterministic() {
    let mut sys = System::new();
    sys.add(|ctx| async move {
        ctx.send(1, "a", Model::P2p);
        let x = ctx.recv(|_| true).await;
        ctx.send(1, x, Model::Cd);
    });
    let traces = [vec![S, v("hi")]];
    let a = sys.next(&traces);
    let b = sys.next(&traces);
    assert_eq!(a, b, "same trace must yield the same labels");
    assert_send(&a[0], 1, "hi");
}

// -- Boundedness ------------------------------------------------------------------

/// An unbounded awaiting loop is capped by the event budget: past the budget the next
/// event becomes an `Error` instead of diverging.
#[test]
fn event_budget_caps_divergent_loop() {
    let mut sys = System::new().with_max_events(3);
    sys.add(|ctx| async move {
        loop {
            let _ = ctx.recv(|_| true).await;
        }
    });
    // Two resolved receives: still enumerating a third receive.
    assert_recv(&sys.next(&[vec![v("x"), v("x")]])[0]);
    // Three resolved receives: the budget is exhausted, so we get an Error.
    match &sys.next(&[vec![v("x"), v("x"), v("x")]])[0] {
        ThreadNext::Next(Label::Error { .. }) => {}
        other => panic!("expected Error at budget, got {other:?}"),
    }
}

/// A budget error at an already-committed position must be `Finished`, not `Error`.
/// Once a trace is in error, extending it stays in error, so a divergent body does not
/// re-emit `Error` forever.
#[test]
fn committed_budget_error_finishes() {
    let mut sys = System::new().with_max_events(3);
    sys.add(|ctx| async move {
        loop {
            let _ = ctx.recv(|_| true).await;
        }
    });
    // Four resolved receives: the budget error falls inside the trace (committed), so
    // the thread finishes rather than re-emitting an error.
    assert_finished(&sys.next(&[vec![v("x"), v("x"), v("x"), v("x")]])[0]);
}

/// The receive budget bounds an infinite event loop from outside the body: the thread's
/// `max_recvs`-th receive is its last event, and the next one makes it `Finished` - a
/// truncation, not an `Error` (unlike the event budget above).
#[test]
fn recv_budget_truncates_infinite_loop() {
    let mut sys = System::new();
    let tid = sys.add(|ctx| async move {
        loop {
            let _ = ctx.recv(|_| true).await;
        }
    });
    sys.set_max_recvs(tid, 2);
    // Receives 1 and 2 are enumerated as usual.
    assert_recv(&sys.next(&[vec![]])[0]);
    assert_recv(&sys.next(&[vec![v("x")]])[0]);
    // The third would exceed the budget: the thread has no next event.
    assert_finished(&sys.next(&[vec![v("x"), v("x")]])[0]);
}

/// The budget counts receives, not events: sends between them are unaffected, and it is
/// the *receives reached during the replay* that count (so the bound is a function of the
/// trace, not of how often the body was polled).
#[test]
fn recv_budget_counts_receives_only() {
    let mut sys = System::new();
    let tid = sys.add(|ctx| async move {
        loop {
            ctx.send(0, "m", Model::P2p);
            let _ = ctx.recv(|_| true).await;
        }
    });
    sys.set_max_recvs(tid, 1);
    assert_send(&sys.next(&[vec![]])[0], 0, "m");
    assert_recv(&sys.next(&[vec![S]])[0]);
    // Budget spent: the loop's second send is still emitted (sends are not counted), and
    // the receive after it ends the thread.
    assert_send(&sys.next(&[vec![S, v("x")]])[0], 0, "m");
    assert_finished(&sys.next(&[vec![S, v("x"), S]])[0]);
}

/// A thread with no declared budget is unbounded (the default), and a budget on one
/// thread does not leak into another.
#[test]
fn recv_budget_is_per_thread() {
    let mut sys = System::new();
    let bounded = sys.add(|ctx| async move {
        loop {
            let _ = ctx.recv(|_| true).await;
        }
    });
    sys.add(|ctx| async move {
        loop {
            let _ = ctx.recv(|_| true).await;
        }
    });
    sys.set_max_recvs(bounded, 1);
    let next = sys.next(&[vec![v("x")], vec![v("x")]]);
    assert_finished(&next[0]);
    assert_recv(&next[1]);
}

/// Awaiting a future that is not `ctx.recv` is outside the contract and is reported as
/// an error, never a silent Finished.
#[test]
fn foreign_future_is_reported_as_error() {
    let mut sys = System::new();
    sys.add(|_ctx| async move {
        // A foreign future that never resolves synchronously.
        std::future::pending::<()>().await;
    });
    match &sys.next(&[vec![]])[0] {
        ThreadNext::Next(Label::Error { msg }) => assert!(msg.contains("foreign")),
        other => panic!("expected foreign-future Error, got {other:?}"),
    }
}

// -- A whole system as a Program --------------------------------------------------

/// s+s+r wired as a `Program`: T0,T1 send to T2, which receives once.
fn ssr_system() -> System {
    let mut sys = System::new();
    sys.add(|ctx| async move { ctx.send(2, "1", Model::P2p) });
    sys.add(|ctx| async move { ctx.send(2, "2", Model::P2p) });
    sys.add(|ctx| async move {
        let _ = ctx.recv(|_| true).await;
    });
    sys
}

#[test]
fn ssr_program_initial_events() {
    let sys = ssr_system();
    assert_eq!(sys.num_threads(), 3);
    let out = sys.next(&[vec![], vec![], vec![]]);
    assert_send(&out[0], 2, "1");
    assert_send(&out[1], 2, "2");
    assert_recv(&out[2]);
}

#[test]
fn ssr_program_after_reading_first_send() {
    let sys = ssr_system();
    // Both sends committed; T2's receive read T0's message "1".
    let out = sys.next(&[vec![S], vec![S], vec![v("1")]]);
    assert_finished(&out[0]);
    assert_finished(&out[1]);
    assert_finished(&out[2]);
}

#[test]
fn ssr_program_after_reading_second_send() {
    let sys = ssr_system();
    // Symmetric: T2 read T1's message "2".
    let out = sys.next(&[vec![S], vec![S], vec![v("2")]]);
    assert_finished(&out[0]);
    assert_finished(&out[1]);
    assert_finished(&out[2]);
}

// -- `possible_future` declarations (H1) -------------------------------------------------
//
// The coroutine runtime cannot enumerate a value-dependent body's remaining events, so
// `Program::possible_future` is opt-in: undeclared processes keep answering `None`
// ("unknown", always safe) and a declaration supplies a sound over-approximation of the
// labels *after* the thread's next event. These tests pin both halves of the contract.

/// `T0: send("a" -> T1)`, `T1: recv(== "a")` — a two-event system whose whole future is
/// trivially declarable (nothing follows either event).
fn declared_pair() -> System {
    let mut sys = System::new();
    let t0 = sys.add(|c: must::Ctx| async move {
        c.send_within(1, "a", Model::Asyn, Window::new(10, 20));
    });
    let t1 = sys.add(|c: must::Ctx| async move {
        c.recv(|x: &str| x == "a").await;
    });
    // Nothing follows the single event of either thread.
    sys.declare_future(t0, |_| Vec::new());
    sys.declare_future(t1, |_| Vec::new());
    sys
}

#[test]
fn undeclared_future_is_unknown() {
    let sys = declared_pair_undeclared();
    assert!(sys.possible_future(0, &[]).is_none());
    assert!(sys.possible_future(1, &[]).is_none());
}

fn declared_pair_undeclared() -> System {
    let mut sys = System::new();
    sys.add(|c: must::Ctx| async move {
        c.send_within(1, "a", Model::Asyn, Window::new(10, 20));
    });
    sys.add(|c: must::Ctx| async move {
        c.recv(|x: &str| x == "a").await;
    });
    sys
}

/// Position 0 of the answer is the thread's *exact* next label (the positional half of the
/// `Program::possible_future` contract, which `force_source` condition (3b) relies on).
#[test]
fn declared_future_head_is_the_next_label() {
    let sys = declared_pair();
    let f0 = sys.possible_future(0, &[]).expect("declared");
    assert_eq!(f0.len(), 1, "one label: the next send, nothing after it");
    assert_send(&ThreadNext::Next(f0[0].clone()), 1, "a");

    let f1 = sys.possible_future(1, &[]).expect("declared");
    assert_eq!(f1.len(), 1);
    assert!(f1[0].is_recv(), "T1's next event is its receive");
}

/// A finished thread's exact future is empty, whatever the declaration says.
#[test]
fn declared_future_of_a_finished_thread_is_empty() {
    let mut sys = declared_pair();
    // Declare a (deliberately over-broad) alphabet for T0 and check it is *not* returned
    // once the thread is finished.
    sys.declare_alphabet(0, [Label::send(Model::Asyn, 1, "a")]);
    assert_eq!(sys.possible_future(0, &[S]), Some(Vec::new()));
}

/// The payoff: with the future declared, `forced_closure` may force a blocking receive whose
/// source is statically unavoidable — something it can never do for an undeclared `System`
/// (`possible_future = None` ⇒ `force_source` bails, T2_PLAN §4 / C1 rule).
#[test]
fn declared_future_lets_the_closure_force_a_blocking_receive() {
    use must::time::forced_closure;
    use must::ExecutionGraph;

    let send = Label::send_within(Model::Asyn, 1, "a", Window::new(10, 20));
    let recv_id = must::event::EventId::new(1, 0);

    let mut g0 = ExecutionGraph::new();
    g0.add_event(0, send.clone());

    let declared = forced_closure(&g0, &declared_pair(), &[0, 1]);
    assert!(
        declared.contains(recv_id),
        "with a declared future the unavoidable receive is forced onto the closure"
    );
    assert_eq!(
        declared.reads_from(recv_id),
        Some(must::event::EventId::new(0, 0))
    );

    let undeclared = forced_closure(&g0, &declared_pair_undeclared(), &[0, 1]);
    assert!(
        !undeclared.contains(recv_id),
        "an undeclared future must keep the C1-safe behaviour: no forced blocking receive"
    );
}

/// A declaration that *does* list a competing future receive must block the force again —
/// the over-approximation is what makes `force_source` conservative, so a coarser
/// declaration may only force less, never more.
#[test]
fn coarser_declaration_forces_less() {
    use must::time::forced_closure;
    use must::ExecutionGraph;

    let mut sys = System::new();
    sys.add(|c: must::Ctx| async move {
        c.send_within(1, "a", Model::Asyn, Window::new(10, 20));
    });
    sys.add(|c: must::Ctx| async move {
        c.recv(|x: &str| x == "a").await;
    });
    sys.declare_future(0, |_| Vec::new());
    // Over-broad but sound: "T1 may run another receive accepting anything later".
    sys.declare_alphabet(1, [Label::recv(must::event::Pred::any())]);

    let mut g0 = ExecutionGraph::new();
    g0.add_event(
        0,
        Label::send_within(Model::Asyn, 1, "a", Window::new(10, 20)),
    );
    let closure = forced_closure(&g0, &sys, &[0, 1]);
    assert!(
        !closure.contains(must::event::EventId::new(1, 0)),
        "a second possible consumer in the declared future blocks the force (condition 3b)"
    );
}

#[test]
fn recv_any_replay_preserves_predicate_tags_annotations_and_receive_budgets() {
    fn make(any: bool, budget: usize) -> System {
        let mut system = System::new();
        system.add(move |c| async move {
            c.insert_label("start");
            let first = if any {
                c.recv_timeout_any().await
            } else {
                c.recv_timeout(|_| true).await
            };
            c.insert_label(first.as_deref().unwrap_or("empty"));
            let second = if any {
                c.recv_any().await
            } else {
                c.recv(|_| true).await
            };
            c.insert_label(second.as_str());
            c.send(0, second, Model::Asyn);
        });
        system.set_max_recvs(0, budget);
        system
    }
    let cases = [
        vec![],
        vec![S],
        vec![v("first")],
        vec![S, v("second")],
        vec![v("first"), v("second")],
        vec![v("first"), S],
        vec![S, S],
        vec![S, v("second"), S],
        vec![v("first"), v("second"), S],
    ];
    for budget in 0..=2 {
        let ordinary = make(false, budget);
        let optimized = make(true, budget);
        for trace in &cases {
            if (budget < 2 && trace.len() > budget) || trace.len() > budget + 1 {
                continue;
            }
            let traces = vec![trace.clone()];
            let expected = ordinary.next(&traces);
            let actual = optimized.next(&traces);
            assert_eq!(actual, expected);
            assert_eq!(optimized.labels(&traces), ordinary.labels(&traces));
            if let ThreadNext::Next(Label::Recv { pred, .. }) = &actual[0] {
                assert!(pred.repr().starts_with("recv#"));
                for value in [
                    "",
                    "message",
                    "\u{043f}\u{0440}\u{0438}\u{0432}\u{0435}\u{0442}",
                ] {
                    assert!(pred.test(value));
                    assert!(pred.test_sym(value.into()));
                }
            }
        }
    }
}

#[test]
fn recv_any_exploration_preserves_exact_terminal_sets() {
    fn make(any: bool) -> System {
        let mut system = System::new();
        system.add(|c| async move {
            c.send(1, "a", Model::Asyn);
            c.send(1, "b", Model::Asyn);
        });
        system.add(move |c| async move {
            let first = if any {
                c.recv_timeout_any().await
            } else {
                c.recv_timeout(|_| true).await
            };
            c.insert_label(first.as_deref().unwrap_or("empty"));
            let second = if any {
                c.recv_any().await
            } else {
                c.recv(|_| true).await
            };
            c.send(0, second, Model::Asyn);
        });
        system.add(|c| async move { c.send(1, "c", Model::Asyn) });
        system
    }
    for priorities in [vec![0, 1, 2], vec![1, 2, 0], vec![2, 1, 0]] {
        let ordinary = must::ExecutionCollector::new();
        let optimized = must::ExecutionCollector::new();
        let config = must::Config::default().with_priorities(priorities);
        must::explore(|| make(false), &ordinary, config.clone());
        must::explore(|| make(true), &optimized, config);
        assert_eq!(optimized.terminal_keys(), ordinary.terminal_keys());
    }
}

#[test]
fn live_await_checkpoints_resume_without_replaying_and_invalidate_on_siblings_and_cuts() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    let factories = Arc::new(AtomicUsize::new(0));
    let mut system = System::new().with_incremental_replay(true);
    let counter = factories.clone();
    system.add(move |c| {
        counter.fetch_add(1, Ordering::Relaxed);
        async move {
            let first = c.recv_any().await;
            let choice = c.nondet(["left", "right"]).await;
            let last = c.recv_timeout_any().await;
            c.send(
                0,
                format!("{first}/{choice}/{}", last.as_deref().unwrap_or("empty")),
                Model::Asyn,
            );
        }
    });
    assert_recv(&system.next_thread(0, &[]));
    assert_recv(&system.next_thread(0, &[]));
    assert_eq!(factories.load(Ordering::Relaxed), 1);
    assert!(matches!(
        system.next_thread(0, &[v("a")]),
        ThreadNext::Next(Label::Nondet { .. })
    ));
    assert_recv_nb(&system.next_thread(0, &[v("a"), v("left")]));
    assert_eq!(factories.load(Ordering::Relaxed), 1);
    assert_send(
        &system.next_thread(0, &[v("a"), v("left"), S]),
        0,
        "a/left/empty",
    );
    assert_eq!(factories.load(Ordering::Relaxed), 1);
    // A send's Rust tail has already run; it is deliberately not a checkpoint.
    assert_send(
        &system.next_thread(0, &[v("a"), v("left"), v("b")]),
        0,
        "a/left/b",
    );
    assert_eq!(factories.load(Ordering::Relaxed), 2);
    assert_recv_nb(&system.next_thread(0, &[v("a"), v("right")]));
    assert_eq!(factories.load(Ordering::Relaxed), 3);
    assert_recv(&system.next_thread(0, &[]));
    assert_eq!(factories.load(Ordering::Relaxed), 4);
    assert_send(
        &system.next_thread(0, &[v("alternate"), v("right"), v("last")]),
        0,
        "alternate/right/last",
    );
    assert_eq!(factories.load(Ordering::Relaxed), 5);
}

#[test]
fn live_checkpoints_preserve_budgets_predicates_and_fresh_annotation_replay() {
    fn make(live: bool, events: usize, receives: usize) -> System {
        let mut system = System::new()
            .with_incremental_replay(live)
            .with_max_events(events);
        system.add(|c| async move {
            c.insert_label("before-first");
            let first = c.recv_timeout(|v| v != "invalid").await;
            c.insert_label(first.as_deref().unwrap_or("empty"));
            c.insert_label("same-position");
            let choice = c.nondet(["left", "right"]).await;
            c.insert_label(choice);
            let second = c.recv(|v| v.starts_with('s')).await;
            c.send(0, second, Model::Asyn);
            c.insert_label("after-send");
            let _ = c.recv_timeout_any().await;
            c.insert_label("finished");
        });
        system.set_max_recvs(0, receives);
        system
    }
    let paths = [
        vec![S, v("left"), v("second"), S, S],
        vec![v("first"), v("right"), v("second"), S, v("last")],
        vec![v("first"), v("left"), S],
    ];
    for receives in 0..=3 {
        for events in 0..=6 {
            let live = make(true, events, receives);
            let replay = make(false, events, receives);
            for path in &paths {
                let receive_cut = match receives {
                    0 => 0,
                    1 => 2,
                    2 => 4,
                    _ => path.len(),
                };
                let limit = path.len().min(events).min(receive_cut);
                for length in 0..=limit {
                    let trace = &path[..length];
                    let expected = replay.next_thread(0, trace);
                    let actual = live.next_thread(0, trace);
                    assert_eq!(actual, expected);
                    if let (
                        ThreadNext::Next(Label::Recv { pred: a, .. }),
                        ThreadNext::Next(Label::Recv { pred: b, .. }),
                    ) = (&actual, &expected)
                    {
                        for value in ["invalid", "first", "second", "no"] {
                            assert_eq!(a.test(value), b.test(value));
                        }
                    }
                    let traces = [trace.to_vec()];
                    assert_eq!(live.labels(&traces), replay.labels(&traces));
                }
            }
        }
    }
}

#[test]
fn live_checkpoints_do_not_resume_send_tails_completed_bodies_or_foreign_awaits() {
    fn make(live: bool) -> System {
        let mut system = System::new().with_incremental_replay(live);
        system.add(|c| async move {
            let first = c.recv_any().await;
            let mut state = vec![first];
            c.send(0, state.len().to_string(), Model::Asyn);
            state.push("second".into());
            c.send(0, state.len().to_string(), Model::Asyn);
            c.insert_label("after-burst");
            let next = c.recv_any().await;
            c.assert_that(next != "bad", "bad value");
        });
        system.add(|c| async move {
            c.send(0, "only-send", Model::Asyn);
        });
        system.add(|c| async move {
            let _ = c.recv_any().await;
            std::future::pending::<()>().await;
        });
        system
    }
    let live = make(true);
    let replay = make(false);
    for trace in [
        vec![],
        vec![v("first")],
        vec![v("first"), S],
        vec![v("first"), S, S],
        vec![v("first"), S, S, v("bad")],
        vec![v("first"), S, S, v("bad"), S],
        vec![v("first"), S, S, v("good")],
    ] {
        assert_eq!(live.next_thread(0, &trace), replay.next_thread(0, &trace));
        assert_eq!(live.next_thread(0, &trace), replay.next_thread(0, &trace));
    }
    for tid in [1, 2] {
        let first = if tid == 1 { S } else { v("value") };
        for trace in [vec![], vec![first]] {
            assert_eq!(
                live.next_thread(tid, &trace),
                replay.next_thread(tid, &trace)
            );
            assert_eq!(
                live.next_thread(tid, &trace),
                replay.next_thread(tid, &trace)
            );
        }
    }
}

#[test]
fn live_checkpoints_drop_on_invalidation_and_keep_threads_independent() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    struct Guard(Arc<AtomicUsize>);
    impl Drop for Guard {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }
    let drops = Arc::new(AtomicUsize::new(0));
    let mut system = System::new().with_incremental_replay(true);
    for _ in 0..2 {
        let drops = drops.clone();
        system.add(move |c| {
            let guard = Guard(drops.clone());
            async move {
                let _guard = guard;
                let _ = c.recv_any().await;
                let _ = c.recv_any().await;
            }
        });
    }
    assert_recv(&system.next_thread(0, &[]));
    assert_recv(&system.next_thread(1, &[]));
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    assert_recv(&system.next_thread(0, &[v("a")]));
    assert_recv(&system.next_thread(1, &[]));
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    assert_recv(&system.next_thread(0, &[]));
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    system.set_max_recvs(1, 0);
    assert_eq!(drops.load(Ordering::Relaxed), 2);
    assert!(system.next_thread(1, &[]).is_finished());
    assert_eq!(drops.load(Ordering::Relaxed), 3);
    drop(system);
    assert_eq!(drops.load(Ordering::Relaxed), 4);
}

#[test]
fn live_checkpoint_exploration_preserves_all_terminal_graphs_and_annotations() {
    fn make(live: bool) -> System {
        let mut system = System::new().with_incremental_replay(live);
        system.add(|c| async move {
            c.send(1, "a", Model::Asyn);
            c.send(1, "b", Model::Asyn);
        });
        system.add(|c| async move {
            let first = c.recv_timeout_any().await;
            c.insert_label(first.as_deref().unwrap_or("empty"));
            let choice = c.nondet(["good", "bad"]).await;
            let second = c.recv_any().await;
            c.insert_label(second.as_str());
            c.send(0, second, Model::Asyn);
            c.assert_that(choice != "bad", "chosen failure");
        });
        system.add(|c| async move {
            c.send(1, "c", Model::Asyn);
        });
        system
    }
    fn annotated(collector: &must::ExecutionCollector) -> Vec<String> {
        let annotations = collector
            .full()
            .into_iter()
            .chain(collector.blocked())
            .chain(collector.errors())
            .map(|execution| {
                format!(
                    "{}{:?}",
                    execution.graph().canonical_key(),
                    execution.labels()
                )
            })
            .collect();
        sorted_runtime_keys(annotations)
    }
    for priorities in [vec![0, 1, 2], vec![1, 2, 0]] {
        for threads in [1, 4] {
            for limit in [None, Some(2)] {
                let replay = must::ExecutionCollector::new();
                let live = must::ExecutionCollector::new();
                let mut config = must::Config::default()
                    .collect_errors()
                    .with_priorities(priorities.clone())
                    .with_threads(threads);
                config.max_sends = limit;
                must::explore(|| make(false), &replay, config.clone());
                must::explore(|| make(true), &live, config);
                assert_eq!(sorted_runtime_keys(live.terminal_keys()), sorted_runtime_keys(replay.terminal_keys()), "terminal multiset: priorities={priorities:?}, threads={threads}, limit={limit:?}");
                assert_eq!(
                    sorted_runtime_keys(live.error_keys()),
                    sorted_runtime_keys(replay.error_keys()),
                    "error multiset: priorities={priorities:?}, threads={threads}, limit={limit:?}"
                );
                assert_eq!(
                    annotated(&live),
                    annotated(&replay),
                    "annotations: priorities={priorities:?}, threads={threads}, limit={limit:?}"
                );
            }
        }
    }
}

#[test]
fn live_checkpoints_never_mutate_an_emitted_custom_predicates_local_state() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    fn make(live: bool) -> System {
        let mut system = System::new().with_incremental_replay(live);
        system.add(|c| async move {
            c.send(2, "before", Model::Asyn);
        });
        system.add(|c| async move {
            c.send(2, "after", Model::Asyn);
        });
        system.add(|c| async move {
            let state = Arc::new(AtomicUsize::new(0));
            let captured = state.clone();
            let value = c
                .recv(move |v| captured.load(Ordering::Relaxed) == 0 && v == "before")
                .await;
            state.store(1, Ordering::Relaxed);
            let choice = c.nondet(["one", "two"]).await;
            state.store(2, Ordering::Relaxed);
            c.send(0, format!("{value}/{choice}"), Model::Asyn);
        });
        system
    }
    let live = make(true);
    let ThreadNext::Next(Label::Recv { pred, .. }) = live.next_thread(2, &[]) else {
        panic!("expected receive")
    };
    assert!(pred.test("before"));
    assert!(matches!(
        live.next_thread(2, &[v("before")]),
        ThreadNext::Next(Label::Nondet { .. })
    ));
    assert_send(
        &live.next_thread(2, &[v("before"), v("one")]),
        0,
        "before/one",
    );
    assert!(
        pred.test("before"),
        "the already emitted predicate must retain its original local state"
    );
    assert!(!pred.test("after"));
    for threads in [1, 4] {
        let live = must::ExecutionCollector::new();
        let replay = must::ExecutionCollector::new();
        let config = must::Config::default()
            .with_threads(threads)
            .with_priorities(vec![2, 0, 1]);
        must::explore(|| make(true), &live, config.clone());
        must::explore(|| make(false), &replay, config);
        assert_eq!(
            sorted_runtime_keys(live.terminal_keys()),
            sorted_runtime_keys(replay.terminal_keys()),
            "frozen custom predicates: threads={threads}"
        );
        assert_eq!(live.full_count(), 2);
        for execution in live.full() {
            assert!(must::consistent(execution.graph()));
        }
    }
}

fn sorted_runtime_keys(mut keys: Vec<String>) -> Vec<String> {
    keys.sort();
    keys
}

fn check_batch_against_replay(
    batched: &System,
    replay: &System,
    trace: &[Option<Val>],
) -> must::runtime::ReplayBatch {
    let batch = batched.next_thread_batch(0, trace);
    assert!(!batch.steps.is_empty());
    let mut prefix = trace.to_vec();
    for (offset, next) in batch.steps.iter().enumerate() {
        let expected = replay.next_thread(0, &prefix);
        assert_eq!(*next, expected);
        if let (
            ThreadNext::Next(Label::Recv { pred: a, .. }),
            ThreadNext::Next(Label::Recv { pred: b, .. }),
        ) = (next, &expected)
        {
            for value in ["a", "b", "before", "after", "invalid"] {
                assert_eq!(a.test(value), b.test(value));
            }
        }
        let labels: Vec<_> = batch
            .labels
            .iter()
            .filter(|label| label.position <= prefix.len())
            .cloned()
            .collect();
        assert_eq!(labels, replay.labels(&[prefix.clone()]));
        if offset + 1 < batch.steps.len() {
            assert!(matches!(next, ThreadNext::Next(Label::Send { .. })));
            prefix.push(S);
        }
    }
    batch
}

#[test]
fn deterministic_send_batches_and_live_awaits_need_one_factory_for_a_linear_path() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    fn make(counter: Arc<AtomicUsize>, live: bool) -> System {
        let mut system = System::new().with_incremental_replay(live);
        system.add(move |c| {
            counter.fetch_add(1, Ordering::Relaxed);
            async move {
                let mut local = vec!["first".to_owned()];
                c.insert_label("before-first");
                c.insert_label("same-position");
                c.send(0, local.len().to_string(), Model::Asyn);
                c.insert_label("after-first");
                c.insert_label("before-second");
                local.push("second".into());
                c.send(0, local.len().to_string(), Model::Asyn);
                c.insert_label("before-receive");
                let reply = c.recv_any().await;
                c.insert_label(reply.as_str());
                c.send(0, reply, Model::Asyn);
                let choice = c.nondet(["left", "right"]).await;
                c.send(0, choice, Model::Asyn);
                let last = c.recv_timeout_any().await;
                c.insert_label(last.as_deref().unwrap_or("empty"));
            }
        });
        system
    }
    let count = Arc::new(AtomicUsize::new(0));
    let batched = make(count.clone(), true);
    let replay_count = Arc::new(AtomicUsize::new(0));
    let replay = make(replay_count.clone(), false);
    let first = check_batch_against_replay(&batched, &replay, &[]);
    assert_eq!(first.steps.len(), 3);
    assert_send(&first.steps[0], 0, "1");
    assert_send(&first.steps[1], 0, "2");
    let repeated = check_batch_against_replay(&batched, &replay, &[S, S]);
    assert_eq!(repeated.steps.len(), 1);
    let second = check_batch_against_replay(&batched, &replay, &[S, S, v("reply")]);
    assert_eq!(second.steps.len(), 2);
    let third = check_batch_against_replay(&batched, &replay, &[S, S, v("reply"), S, v("left")]);
    assert_eq!(third.steps.len(), 2);
    let last =
        check_batch_against_replay(&batched, &replay, &[S, S, v("reply"), S, v("left"), S, S]);
    assert!(last.steps[0].is_finished());
    assert_eq!(count.load(Ordering::Relaxed), 1);
    assert!(replay_count.load(Ordering::Relaxed) >= 8);
    check_batch_against_replay(&batched, &replay, &[S, S, v("other")]);
    assert_eq!(count.load(Ordering::Relaxed), 2);
    check_batch_against_replay(&batched, &replay, &[]);
    assert_eq!(count.load(Ordering::Relaxed), 3);
}

#[test]
fn deterministic_batches_preserve_ready_error_foreign_await_and_budget_boundaries() {
    fn make(live: bool, mode: usize, events: usize, receives: usize) -> System {
        let mut system = System::new()
            .with_incremental_replay(live)
            .with_max_events(events);
        system.add(move |c| async move {
            c.insert_label("before-send");
            c.send(0, "one", Model::Asyn);
            c.insert_label("after-send");
            if mode == 0 {
                c.send(0, "two", Model::Asyn);
                c.insert_label("done");
            }
            if mode == 1 {
                c.assert_that(false, "failure");
                c.insert_label("must-not-leak");
                c.send(0, "must-not-send", Model::Asyn);
            }
            if mode == 2 {
                std::future::pending::<()>().await;
            }
            if mode == 3 {
                let reply = c.recv_timeout_any().await;
                c.insert_label(reply.as_deref().unwrap_or("empty"));
                c.send(0, "after-receive", Model::Asyn);
                let choice = c.nondet(["a", "b"]).await;
                c.insert_label(choice);
                let _ = c.recv_any().await;
                c.insert_label("finished");
            }
        });
        system.set_max_recvs(0, receives);
        system
    }
    for mode in 0..4 {
        for events in 0..=6 {
            for receives in 0..=2 {
                let batched = make(true, mode, events, receives);
                let replay = make(false, mode, events, receives);
                let mut trace = Vec::new();
                for _ in 0..4 {
                    let batch = check_batch_against_replay(&batched, &replay, &trace);
                    trace.extend(std::iter::repeat_n(S, batch.steps.len() - 1));
                    match batch.steps.last().unwrap() {
                        ThreadNext::Next(Label::Recv { blocking, .. }) => {
                            trace.push(if *blocking { v("reply") } else { S })
                        }
                        ThreadNext::Next(Label::Nondet { .. }) => trace.push(v("a")),
                        ThreadNext::Next(Label::Error { .. }) | ThreadNext::Finished => break,
                        _ => panic!("batch must end at an await, error or completion"),
                    }
                }
            }
        }
    }
}

#[test]
fn deterministic_batches_freeze_custom_predicates_and_mix_with_plain_queries() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    fn make(live: bool) -> System {
        let mut system = System::new().with_incremental_replay(live);
        system.add(|c| async move {
            let state = Arc::new(AtomicUsize::new(0));
            c.send(0, "prefix", Model::Asyn);
            let captured = state.clone();
            let first = c
                .recv(move |v| captured.load(Ordering::Relaxed) == 0 && v == "before")
                .await;
            state.store(1, Ordering::Relaxed);
            c.insert_label("first-reply");
            c.send(0, first, Model::Asyn);
            let _ = c.recv_any().await;
            c.send(0, "first-tail", Model::Asyn);
            c.send(0, "second-tail", Model::Asyn);
        });
        system
    }
    let batched = make(true);
    let replay = make(false);
    let batch = check_batch_against_replay(&batched, &replay, &[]);
    let ThreadNext::Next(Label::Recv { pred, .. }) = batch.steps.last().unwrap() else {
        panic!("expected custom boundary")
    };
    assert!(pred.test("before"));
    check_batch_against_replay(&batched, &replay, &[S, v("before")]);
    assert!(pred.test("before"));
    // Resuming a batched Any checkpoint through the plain API must stop at the
    // first synchronous send, even though run-ahead previously reached past it.
    let trace = [S, v("before"), S, v("reply")];
    assert_eq!(
        batched.next_thread(0, &trace),
        replay.next_thread(0, &trace)
    );
    assert_send(&batched.next_thread(0, &trace), 0, "first-tail");
    check_batch_against_replay(&batched, &replay, &[S]);
    assert!(pred.test("before"));
}
