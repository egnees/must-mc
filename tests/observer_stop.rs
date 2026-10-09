use std::sync::atomic::{AtomicUsize, Ordering};

use must::{explore, Config, EventCountingObserver, Execution, ExecutionKind, Observer, System};

const CHOICES: usize = 10;
const TERMINALS: usize = 1 << CHOICES;

fn many_terminals() -> System {
    let mut system = System::new();
    system.add(|ctx| async move {
        for _ in 0..CHOICES {
            ctx.nondet(["0", "1"]).await;
        }
    });
    system
}

#[derive(Default)]
struct StopAfterFirst {
    reported: AtomicUsize,
}

impl Observer for StopAfterFirst {
    fn on_execution(&self, _exec: &Execution, kind: ExecutionKind) {
        assert_eq!(kind, ExecutionKind::Full);
        self.reported.fetch_add(1, Ordering::Relaxed);
    }

    fn should_stop(&self) -> bool {
        self.reported.load(Ordering::Relaxed) > 0
    }
}

#[test]
fn default_observer_does_not_stop() {
    for threads in [1, 12] {
        let observer = EventCountingObserver::new();
        explore(
            many_terminals,
            &observer,
            Config::default().with_threads(threads),
        );
        assert_eq!(observer.full(), TERMINALS);
        assert_eq!(observer.errors(), 0);
    }
}

#[test]
fn observer_stops_sequential_search_without_reclassifying_terminal() {
    let observer = (StopAfterFirst::default(), EventCountingObserver::new());
    explore(many_terminals, &observer, Config::default());
    assert_eq!(observer.0.reported.load(Ordering::Relaxed), 1);
    assert_eq!(observer.1.full(), 1);
    assert_eq!(observer.1.errors(), 0);
}

#[test]
fn observer_stops_parallel_search_through_second_tuple_member() {
    let observer = (EventCountingObserver::new(), StopAfterFirst::default());
    explore(
        many_terminals,
        &observer,
        Config::default().with_threads(12),
    );
    let reported = observer.1.reported.load(Ordering::Relaxed);
    // In-flight workers may report more than the first terminal, but the remaining
    // search must be abandoned, with every reported outcome retaining its kind.
    assert!((1..TERMINALS).contains(&reported));
    assert_eq!(observer.0.full(), reported);
    assert_eq!(observer.0.errors(), 0);
}
