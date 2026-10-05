//! A send budget bounds each explored prefix, never the accumulated replay work.
use std::sync::Mutex;

use must::{
    explore, Config, CountingObserver, Ctx, ExecutionGraph, Model, Observer, System, Window,
};

#[derive(Default)]
struct CutPrefixes(Mutex<Vec<(usize, usize)>>);

impl Observer for CutPrefixes {
    fn on_send_limit(&self, graph: &ExecutionGraph, limit: usize) {
        self.0.lock().unwrap().push((graph.sends().len(), limit));
    }
}

fn sends(count: usize) -> System {
    let mut system = System::new();
    system.add(move |ctx: Ctx| async move {
        for _ in 0..count {
            ctx.send(0, "message", Model::Asyn);
        }
    });
    system
}

#[test]
fn zero_exact_and_over_budget_are_distinct_from_terminals() {
    for (count, limit, full, cuts) in [(0, 0, 1, 0), (1, 0, 0, 1), (2, 2, 1, 0), (3, 2, 0, 1)] {
        let observer = (CountingObserver::new(), CutPrefixes::default());
        explore(
            || sends(count),
            &observer,
            Config::default().with_max_sends(limit),
        );
        assert_eq!(observer.0.full(), full, "sends={count}, limit={limit}");
        assert_eq!(observer.0.send_limit_hits(), cuts);
        assert_eq!(observer.0.errors(), 0);
        assert_eq!(observer.0.blocked(), 0);
        assert_eq!(observer.0.filtered(), 0);
        assert_eq!(*observer.1 .0.lock().unwrap(), vec![(limit, limit); cuts]);
    }
}

#[test]
fn default_does_not_limit_sends() {
    assert_eq!(Config::default().max_sends, None);
    let observer = CountingObserver::new();
    explore(|| sends(5), &observer, Config::default());
    assert_eq!(observer.full(), 1);
    assert_eq!(observer.send_limit_hits(), 0);
}

fn ping_pong(extra_send: bool) -> System {
    let mut system = System::new();
    system.add(move |ctx: Ctx| async move {
        ctx.send(1, "request", Model::P2p);
        ctx.recv(|_| true).await;
        if extra_send {
            ctx.send(1, "another request", Model::P2p);
        }
    });
    system.add(|ctx: Ctx| async move {
        ctx.recv(|_| true).await;
        ctx.send(0, "response", Model::P2p);
    });
    system
}

#[test]
fn all_processes_share_budget_including_already_consumed_sends() {
    let observer = (CountingObserver::new(), CutPrefixes::default());
    explore(
        || ping_pong(true),
        &observer,
        Config::default().with_max_sends(2),
    );
    assert_eq!(observer.0.send_limit_hits(), 1);
    assert_eq!(observer.0.full(), 0);
    assert_eq!(*observer.1 .0.lock().unwrap(), [(2, 2)]);
}

#[test]
fn exact_budget_allows_receivers_to_finish_and_replay_is_not_charged() {
    let observer = CountingObserver::new();
    explore(
        || ping_pong(false),
        &observer,
        Config::default().with_max_sends(2),
    );
    assert_eq!(observer.full(), 1);
    assert_eq!(observer.blocked(), 0);
    assert_eq!(observer.send_limit_hits(), 0);
}

#[test]
fn choices_and_local_markers_do_not_consume_send_budget() {
    let observer = CountingObserver::new();
    explore(
        || {
            let mut system = System::new();
            system.add(|ctx: Ctx| async move {
                ctx.nondet(["first", "second"]).await;
                ctx.insert_label("local-delivery");
                ctx.insert_label("another-local-action");
            });
            system
        },
        &observer,
        Config::default().with_max_sends(0),
    );
    assert_eq!(observer.full(), 2);
    assert_eq!(observer.send_limit_hits(), 0);
}

#[test]
fn cut_branch_does_not_stop_siblings_or_other_workers() {
    for threads in [1, 4] {
        let observer = (CountingObserver::new(), CutPrefixes::default());
        explore(
            || {
                let mut system = System::new();
                system.add(|ctx: Ctx| async move {
                    let choice = ctx.nondet(["a-cut", "b-full", "c-cut", "d-full"]).await;
                    if choice.ends_with("cut") {
                        ctx.send(0, "over budget", Model::Asyn);
                    }
                });
                system
            },
            &observer,
            Config::default().with_max_sends(0).with_threads(threads),
        );
        assert_eq!(observer.0.full(), 2, "threads={threads}");
        assert_eq!(observer.0.send_limit_hits(), 2, "threads={threads}");
        assert_eq!(observer.0.errors(), 0);
        assert_eq!(*observer.1 .0.lock().unwrap(), [(0, 0), (0, 0)]);
    }
}

#[test]
fn feasible_timed_prefix_reports_cut_instead_of_a_filtered_terminal() {
    for certified in [false, true] {
        let observer = CountingObserver::new();
        let config = Config::default()
            .collect_errors()
            .with_mailbox_time()
            .with_time_filter()
            .with_max_sends(1);
        let config = if certified {
            config.with_certified_time()
        } else {
            config
        };
        explore(
            || {
                let mut system = System::new();
                system.add(|ctx: Ctx| async move {
                    ctx.send_within(0, "one", Model::P2p, Window::new(1, 1));
                    ctx.send_within(0, "two", Model::P2p, Window::new(2, 2));
                });
                system
            },
            &observer,
            config,
        );
        assert_eq!(observer.send_limit_hits(), 1, "certified={certified}");
        assert_eq!(observer.full(), 0);
        assert_eq!(observer.blocked(), 0);
        assert_eq!(observer.errors(), 0);
        assert_eq!(observer.filtered(), 0);
    }
}
