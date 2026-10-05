//! Multi-threaded driver for the explorer.
//!
//! DPOR subtrees are independent: the explorer is stateless (every branch works on a clone
//! of the graph), so exploring `Visit_P(G)` for a consistent `G` is a pure function of
//! `(G, program, priorities)`. The search tree is therefore embarrassingly parallel - the
//! driver hands out subtrees to a pool of workers.
//!
//! Each worker builds its own program instance (via `make_program`, so the `!Send`
//! `System` and its coroutine futures never cross a thread) and runs the ordinary recursive
//! [`Explorer`](super::Explorer); only `Send` execution graphs travel between threads,
//! through a shared work queue. A worker recurses the first child of every node inline and
//! sheds a later sibling to the queue only when another worker is idle, so while all workers
//! are busy none touches the queue.
//!
//! The single `observer` is shared by every worker; it sees the same *set* of executions
//! as the sequential [`explore`](super::explore), only in a nondeterministic order.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use crate::graph::ExecutionGraph;
use crate::observer::{set_worker_id, Observer};
use crate::program::Program;

use super::{is_permutation, Config, Explorer};

/// Work queue plus the count that decides when the run is over.
struct Shared {
    queue: VecDeque<ExecutionGraph>,
    /// Tasks pushed but not yet completed (queued or in flight); the run ends when this
    /// reaches 0.
    outstanding: usize,
}

/// Shared coordination state for a parallel `explore` run. Held in an `Arc` by every worker
/// and by each worker's [`Explorer`](super::Explorer).
pub(crate) struct Spawner {
    shared: Mutex<Shared>,
    cvar: Condvar,
    /// Workers currently blocked waiting for work. A busy worker sheds a subtree only while
    /// this is `> 0`; while every worker is busy it stays 0, so
    /// [`wants_work`](Self::wants_work) returns false and no busy worker touches the queue.
    hungry: AtomicUsize,
    /// Aborts the whole run (execution cap hit, or `stop_on_error` first error).
    pub(crate) stop: AtomicBool,
    /// Global full+blocked terminal count for the `max_executions` cap (best-effort).
    terminal_count: AtomicUsize,
}

impl Spawner {
    fn new() -> Self {
        Spawner {
            shared: Mutex::new(Shared {
                queue: VecDeque::new(),
                outstanding: 0,
            }),
            cvar: Condvar::new(),
            hungry: AtomicUsize::new(0),
            stop: AtomicBool::new(false),
            terminal_count: AtomicUsize::new(0),
        }
    }

    /// Whether to shed a sibling subtree now: only when some worker is idle.
    pub(crate) fn wants_work(&self) -> bool {
        self.hungry.load(Ordering::Relaxed) > 0
    }

    /// Enqueue a subtree root; counts against `outstanding` until it completes.
    pub(crate) fn push(&self, g: ExecutionGraph) {
        let mut s = self.shared.lock().unwrap();
        s.queue.push_back(g);
        s.outstanding += 1;
        drop(s);
        self.cvar.notify_one();
    }

    /// Take the next task, blocking until one is available. `None` when the run is finished
    /// (nothing outstanding) or stopped. While blocked the worker counts itself `hungry` so
    /// busy workers begin shedding.
    fn pop(&self) -> Option<ExecutionGraph> {
        let mut s = self.shared.lock().unwrap();
        loop {
            if self.stop.load(Ordering::Relaxed) {
                return None;
            }
            if let Some(item) = s.queue.pop_front() {
                return Some(item);
            }
            if s.outstanding == 0 {
                return None;
            }
            self.hungry.fetch_add(1, Ordering::Relaxed);
            s = self.cvar.wait(s).unwrap();
            self.hungry.fetch_sub(1, Ordering::Relaxed);
        }
    }

    /// Mark the task just processed as done; wake all waiters if it was the last.
    fn complete(&self) {
        let mut s = self.shared.lock().unwrap();
        s.outstanding -= 1;
        let done = s.outstanding == 0;
        drop(s);
        if done {
            self.cvar.notify_all();
        }
    }

    /// Trip the stop flag and wake every worker so they unwind.
    pub(crate) fn request_stop(&self) {
        self.stop.store(true, Ordering::Relaxed);
        self.cvar.notify_all();
    }

    /// Record one full/blocked terminal globally; returns the new count.
    pub(crate) fn record_terminal(&self) -> usize {
        self.terminal_count.fetch_add(1, Ordering::Relaxed) + 1
    }
}

/// Multi-threaded [`explore`](super::explore): walk every consistent execution graph across
/// `config.threads` worker threads, all sharing one `observer`.
///
/// `make_program` is called once per worker to build that worker's own program instance, so
/// the `!Send` runtime never crosses a thread boundary. All workers share the priority
/// permutation from `config`.
///
/// The *set* of executions the observer sees equals the sequential
/// [`explore`](super::explore)'s; only their order differs. `max_executions` /
/// `stop_on_error` stay honoured but become best-effort: in-flight workers may record a few
/// extra terminals before observing the stop flag, and which error surfaces first is
/// nondeterministic. Use a single thread when that determinism matters.
pub(crate) fn explore_parallel<P, MK, O>(make_program: MK, observer: &O, config: Config)
where
    MK: Fn() -> P + Sync,
    P: Program,
    O: Observer + Sync,
{
    let threads = config.threads.max(1);

    let n = make_program().num_threads();
    let priorities: Vec<_> = config
        .priorities
        .clone()
        .unwrap_or_else(|| (0..n).collect());
    assert!(
        is_permutation(&priorities, n),
        "explore: priorities {priorities:?} must be a permutation of 0..{n}"
    );

    let spawner = Arc::new(Spawner::new());
    spawner.push(ExecutionGraph::new()); // seed: Visit_P(the empty graph)

    thread::scope(|scope| {
        for w in 0..threads {
            let sp = Arc::clone(&spawner);
            let priorities = priorities.clone();
            let stop_on_error = config.stop_on_error;
            let max_executions = config.max_executions;
            let time_filter = config.time_filter;
            let time_predicate = config.time_predicate;
            let time_level = config.time_predicate_level;
            let canon_free = config.time_canon_free;
            let time_zombie = config.time_zombie;
            let make_program = &make_program;
            scope.spawn(move || {
                // Route this worker's tallies to its own shard of a shared observer.
                set_worker_id(w);
                let program = make_program();
                let mut ex = Explorer {
                    program: &program,
                    observer,
                    priorities,
                    stop_on_error,
                    max_executions,
                    time_filter,
                    time_predicate,
                    time_level,
                    canon_free,
                    time_zombie,
                    viable_memo: crate::time::ViableMemo::new(),
                    terminal_count: 0,
                    terminals_recorded: 0,
                    stop: false,
                    fork: Some(Arc::clone(&sp)),
                };
                while let Some(g) = sp.pop() {
                    ex.visit(&g);
                    sp.complete();
                }
            });
        }
    });
}
