//! Stop only after a complete, accepted error execution, including with timing filters.
use must::{
    check_mailbox, eager_feasible, explore, Config, CountingObserver, Ctx, ExecutionCollector,
    Model, System, Window,
};

fn branching_errors() -> System {
    let mut system = System::new();
    system.add(|c: Ctx| async move {
        c.nondet(["a", "b", "c", "d", "e", "f", "g", "h"]).await;
        c.assert_that(false, "bad choice");
    });
    // The error event alone is not a terminal: this send must also be present.
    system.add(|c: Ctx| async move { c.send(0, "suffix", Model::Asyn) });
    system
}

#[test]
fn terminal_stop_records_one_complete_error_and_collect_errors_resets_it() {
    assert!(Config::default().stop_on_error);
    assert!(!Config::default().stop_on_terminal_error);
    let stop = Config::default().with_stop_on_terminal_error();
    assert!(!stop.stop_on_error);
    assert!(stop.stop_on_terminal_error);
    let observer = (CountingObserver::new(), ExecutionCollector::new());
    explore(branching_errors, &observer, stop.clone());
    assert_eq!(observer.0.errors(), 1);
    let errors = observer.1.errors();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].graph().sends().len(), 1);

    let collect = stop.collect_errors();
    assert!(!collect.stop_on_error);
    assert!(!collect.stop_on_terminal_error);
    let observer = CountingObserver::new();
    explore(branching_errors, &observer, collect);
    assert_eq!(observer.errors(), 8);
}

#[test]
fn full_and_blocked_terminals_do_not_stop_the_search() {
    let observer = CountingObserver::new();
    explore(
        || {
            let mut system = System::new();
            system.add(|c: Ctx| async move {
                let choice = c
                    .nondet(["full-a", "full-b", "blocked-a", "blocked-b"])
                    .await;
                if choice.starts_with("blocked") {
                    c.recv(|_| true).await;
                }
            });
            system
        },
        &observer,
        Config::default().with_stop_on_terminal_error(),
    );
    assert_eq!(observer.full(), 2);
    assert_eq!(observer.blocked(), 2);
    assert_eq!(observer.errors(), 0);
}

// The first receiver branch reads slow x and is erroneous but time-infeasible.
// Backward revisits must still reach w and z after rejecting that error terminal.
fn timed_revisit(fail_on_z: bool) -> System {
    let mut system = System::new();
    system.add(move |c: Ctx| async move {
        let value = c.recv(|_| true).await;
        c.assert_that(value != "x" && !(fail_on_z && value == "z"), "bad source");
    });
    system.add(|c: Ctx| async move {
        c.send_within(0, "x", Model::Asyn, Window::new(50, 50));
    });
    system.add(|c: Ctx| async move {
        c.send_within(0, "w", Model::Asyn, Window::new(1, 1));
    });
    system.add(|c: Ctx| async move { c.send(0, "z", Model::Asyn) });
    system
}

#[test]
fn filtered_error_does_not_hide_successful_revisits() {
    let observer = (CountingObserver::new(), ExecutionCollector::new());
    explore(
        || timed_revisit(false),
        &observer,
        Config::default()
            .with_time_filter()
            .with_stop_on_terminal_error(),
    );
    assert_eq!(observer.0.filtered_errors(), 1);
    assert_eq!(observer.0.errors(), 0);
    assert_eq!(observer.0.full(), 2);
    assert!(observer.1.full().iter().all(|e| eager_feasible(e.graph())));
}

#[test]
fn filtered_error_is_skipped_before_stopping_on_a_valid_error() {
    let observer = (CountingObserver::new(), ExecutionCollector::new());
    explore(
        || timed_revisit(true),
        &observer,
        Config::default()
            .with_time_filter()
            .with_stop_on_terminal_error(),
    );
    assert_eq!(observer.0.filtered_errors(), 1);
    assert_eq!(observer.0.errors(), 1);
    assert_eq!(observer.1.error_count(), 1);
    assert!(eager_feasible(observer.1.errors()[0].graph()));
}

#[test]
fn mailbox_and_certified_modes_stop_on_an_accepted_error() {
    for certified in [false, true] {
        let mut config = Config::default().with_mailbox_time().with_time_filter();
        if certified {
            config = config.with_certified_time();
        }
        let observer = (CountingObserver::new(), ExecutionCollector::new());
        explore(
            || {
                let mut system = System::new();
                system.add(|c: Ctx| async move {
                    c.send_within(1, "message", Model::P2p, Window::new(1, 1));
                });
                system.add(|c: Ctx| async move {
                    c.recv_timeout_timed(|_| true, Window::new(2, 2)).await;
                    c.nondet(["a", "b", "c"]).await;
                    c.assert_that(false, "delivered");
                });
                system
            },
            &observer,
            config.with_stop_on_terminal_error(),
        );
        assert_eq!(observer.0.errors(), 1, "certified={certified}");
        assert_eq!(observer.1.error_count(), 1);
        assert!(check_mailbox(observer.1.errors()[0].graph()).is_feasible());
    }
}

#[test]
fn parallel_terminal_stop_cancels_globally() {
    // Each worker can report one in-flight terminal before observing cancellation.
    // No assumption about which worker wins or which nondet choice fails first.
    for threads in [2, 4] {
        let observer = (CountingObserver::new(), ExecutionCollector::new());
        explore(
            branching_errors,
            &observer,
            Config::default()
                .with_time_filter()
                .with_stop_on_terminal_error()
                .with_threads(threads),
        );
        assert!((1..=threads).contains(&observer.0.errors()));
        assert_eq!(observer.0.errors(), observer.1.error_count());
        assert!(observer
            .1
            .errors()
            .iter()
            .all(|e| e.graph().sends().len() == 1));
    }
}
