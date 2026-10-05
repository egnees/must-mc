//! Watching a run as it explores.
//!
//! `explore` returns nothing; everything you learn about a run comes through an
//! [`Observer`]. The explorer notifies it at every interesting step: an event added, an rf
//! choice, an inconsistent graph dropped, a backward revisit performed or rejected, a
//! terminal execution reached, a thread found blocked. Every method has an empty default
//! body, so an observer implements only what it cares about.
//!
//! Callbacks take `&self`, so a single observer is shared across every worker thread of a
//! parallel run (`explore` requires `Observer + Sync`). An observer therefore holds its own
//! interior mutability and picks its own synchronisation: [`NullObserver`] needs none,
//! [`CountingObserver`] shards its counters per worker (no cross-thread contention on the
//! hot path), and the recording observers use a mutex.
//!
//! Four implementations come with the crate: [`NullObserver`] (ignores everything),
//! [`CountingObserver`] (running totals), [`RecordingObserver`] (a flat log of owned step
//! snapshots), and [`ExecutionCollector`] (keeps the terminal executions grouped by
//! outcome). Two observers compose as a tuple `(A, B)`.

use std::cell::Cell;
use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

use crate::event::{EventId, Tid};
use crate::explorer::{Execution, ExecutionKind};
use crate::graph::ExecutionGraph;

/// Callbacks fired by the explorer. Every method defaults to a no-op.
pub trait Observer {
    /// A fresh event `e`, maximal in insertion order, was added to `g`.
    fn on_event_added(&self, _g: &ExecutionGraph, _e: EventId) {}
    /// Receive `r` was pointed at source `src` (`None` means no message) before a
    /// consistency check.
    fn on_rf_choice(&self, _g: &ExecutionGraph, _r: EventId, _src: Option<EventId>) {}
    /// A graph was found inconsistent and dropped.
    fn on_inconsistent(&self, _g: &ExecutionGraph) {}
    /// A backward revisit that sets `rf(r)` to `s` is about to run; `deleted` lists the
    /// events it removes (still including `s`).
    fn on_backward_revisit(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _deleted: &BTreeSet<EventId>,
    ) {
    }
    /// A candidate backward revisit setting `rf(r)` to `s` was rejected.
    fn on_revisit_rejected(&self, _g: &ExecutionGraph, _r: EventId, _s: EventId) {}
    /// A terminal execution (full / blocked / error) was reached.
    fn on_execution(&self, _exec: &Execution, _kind: ExecutionKind) {}
    /// A terminal suppressed by the eager time filter (`Config::time_filter`): the graph is
    /// consistent but not time-realisable. [`on_execution`](Self::on_execution) is *not*
    /// called for it, and it does not count towards `max_executions`.
    fn on_execution_filtered(&self, _exec: &Execution, _kind: ExecutionKind) {}
    /// Thread `tid` is blocked on a receive with no message in `g`.
    fn on_thread_blocked(&self, _g: &ExecutionGraph, _tid: Tid) {}
}

// -- Sharding: routing a shared observer to a per-worker slot ----------------------

thread_local! {
    /// Which worker this thread is, so a shared observer can pick a per-worker shard.
    /// Zero on the main thread and every sequential run.
    static WORKER_ID: Cell<usize> = const { Cell::new(0) };
}

/// Called once by each parallel worker so a shared [`CountingObserver`] routes that
/// worker's tallies to its own shard.
pub(crate) fn set_worker_id(w: usize) {
    WORKER_ID.with(|c| c.set(w));
}

/// This thread's worker id (`0` on the main thread and every sequential run). Lets a
/// shared observer route to a per-worker shard; see [`CountingObserver`] and
/// [`crate::viz::TraceObserver`].
pub(crate) fn worker_id() -> usize {
    WORKER_ID.with(Cell::get)
}

/// Shard count a freshly built [`CountingObserver`] uses: the machine's parallelism, so a
/// shared counter never contends on one cache line during a parallel run. Computed once.
/// Shared with [`crate::viz::TraceObserver`], which shards its trace buffers the same way.
pub(crate) fn default_shards() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// Observer that ignores everything.
#[derive(Clone, Copy, Debug, Default)]
pub struct NullObserver;

impl Observer for NullObserver {}

/// One worker's tallies. Aligned to a cache line so two workers writing adjacent shards
/// never trigger false sharing; each shard is written by a single thread, so its atomics
/// are always uncontended.
#[repr(align(64))]
#[derive(Debug, Default)]
struct Shard {
    events_added: AtomicUsize,
    rf_choices: AtomicUsize,
    inconsistent: AtomicUsize,
    backward_revisits: AtomicUsize,
    revisits_rejected: AtomicUsize,
    full: AtomicUsize,
    blocked: AtomicUsize,
    errors: AtomicUsize,
    filtered_full: AtomicUsize,
    filtered_blocked: AtomicUsize,
    filtered_errors: AtomicUsize,
    threads_blocked: AtomicUsize,
}

/// Running totals of every callback, sharded per worker so counting adds no cross-thread
/// contention under a parallel run. Read a total with the accessor methods, which sum the
/// shards.
#[derive(Debug)]
pub struct CountingObserver {
    shards: Vec<Shard>,
}

impl Default for CountingObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl CountingObserver {
    /// A counter sized for the machine's parallelism, ready to be shared across a parallel
    /// run without contention.
    pub fn new() -> Self {
        Self::with_shards(default_shards())
    }

    /// A counter with an explicit shard count (at least one). Use this to match a known
    /// worker count exactly; [`new`](Self::new) picks a sensible default.
    pub fn with_shards(shards: usize) -> Self {
        CountingObserver {
            shards: (0..shards.max(1)).map(|_| Shard::default()).collect(),
        }
    }

    /// This thread's shard (`worker_id mod shard_count`).
    fn shard(&self) -> &Shard {
        &self.shards[worker_id() % self.shards.len()]
    }

    fn total(&self, pick: impl Fn(&Shard) -> &AtomicUsize) -> usize {
        self.shards
            .iter()
            .map(|s| pick(s).load(Ordering::Relaxed))
            .sum()
    }

    pub fn events_added(&self) -> usize {
        self.total(|s| &s.events_added)
    }
    pub fn rf_choices(&self) -> usize {
        self.total(|s| &s.rf_choices)
    }
    pub fn inconsistent(&self) -> usize {
        self.total(|s| &s.inconsistent)
    }
    pub fn backward_revisits(&self) -> usize {
        self.total(|s| &s.backward_revisits)
    }
    pub fn revisits_rejected(&self) -> usize {
        self.total(|s| &s.revisits_rejected)
    }
    pub fn full(&self) -> usize {
        self.total(|s| &s.full)
    }
    pub fn blocked(&self) -> usize {
        self.total(|s| &s.blocked)
    }
    pub fn errors(&self) -> usize {
        self.total(|s| &s.errors)
    }
    /// Full terminals suppressed by the eager time filter.
    pub fn filtered_full(&self) -> usize {
        self.total(|s| &s.filtered_full)
    }
    /// Blocked terminals suppressed by the eager time filter.
    pub fn filtered_blocked(&self) -> usize {
        self.total(|s| &s.filtered_blocked)
    }
    /// Error terminals suppressed by the eager time filter.
    pub fn filtered_errors(&self) -> usize {
        self.total(|s| &s.filtered_errors)
    }
    /// All time-filtered terminals (full + blocked + error).
    pub fn filtered(&self) -> usize {
        self.filtered_full() + self.filtered_blocked() + self.filtered_errors()
    }
    pub fn threads_blocked(&self) -> usize {
        self.total(|s| &s.threads_blocked)
    }

    /// Total terminal executions (full + blocked).
    pub fn terminal(&self) -> usize {
        self.full() + self.blocked()
    }
}

impl Observer for CountingObserver {
    fn on_event_added(&self, _g: &ExecutionGraph, _e: EventId) {
        self.shard().events_added.fetch_add(1, Ordering::Relaxed);
    }
    fn on_rf_choice(&self, _g: &ExecutionGraph, _r: EventId, _src: Option<EventId>) {
        self.shard().rf_choices.fetch_add(1, Ordering::Relaxed);
    }
    fn on_inconsistent(&self, _g: &ExecutionGraph) {
        self.shard().inconsistent.fetch_add(1, Ordering::Relaxed);
    }
    fn on_backward_revisit(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _deleted: &BTreeSet<EventId>,
    ) {
        self.shard()
            .backward_revisits
            .fetch_add(1, Ordering::Relaxed);
    }
    fn on_revisit_rejected(&self, _g: &ExecutionGraph, _r: EventId, _s: EventId) {
        self.shard()
            .revisits_rejected
            .fetch_add(1, Ordering::Relaxed);
    }
    fn on_execution(&self, _exec: &Execution, kind: ExecutionKind) {
        let shard = self.shard();
        match kind {
            ExecutionKind::Full => &shard.full,
            ExecutionKind::Blocked => &shard.blocked,
            ExecutionKind::Error => &shard.errors,
        }
        .fetch_add(1, Ordering::Relaxed);
    }
    fn on_execution_filtered(&self, _exec: &Execution, kind: ExecutionKind) {
        let shard = self.shard();
        match kind {
            ExecutionKind::Full => &shard.filtered_full,
            ExecutionKind::Blocked => &shard.filtered_blocked,
            ExecutionKind::Error => &shard.filtered_errors,
        }
        .fetch_add(1, Ordering::Relaxed);
    }
    fn on_thread_blocked(&self, _g: &ExecutionGraph, _tid: Tid) {
        self.shard().threads_blocked.fetch_add(1, Ordering::Relaxed);
    }
}

/// One recorded step, as an owned snapshot (no borrow of the live graph).
#[derive(Clone, Debug)]
pub struct Step {
    pub kind: StepKind,
    /// The graph as it stood at this step (owned).
    pub graph: ExecutionGraph,
}

/// The event a [`Step`] captured.
#[derive(Clone, Debug)]
pub enum StepKind {
    EventAdded {
        e: EventId,
    },
    RfChoice {
        r: EventId,
        src: Option<EventId>,
    },
    Inconsistent,
    BackwardRevisit {
        r: EventId,
        s: EventId,
        deleted: Vec<EventId>,
    },
    RevisitRejected {
        r: EventId,
        s: EventId,
    },
    Execution {
        kind: ExecutionKind,
    },
    ExecutionFiltered {
        kind: ExecutionKind,
    },
    ThreadBlocked {
        tid: Tid,
    },
}

/// Flat log of every step, for later rendering. For sequential runs in practice: a
/// parallel run interleaves the workers' steps into one meaningless log.
#[derive(Debug, Default)]
pub struct RecordingObserver {
    steps: Mutex<Vec<Step>>,
}

impl RecordingObserver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.steps.lock().unwrap().len()
    }

    pub fn is_empty(&self) -> bool {
        self.steps.lock().unwrap().is_empty()
    }

    /// A snapshot of the steps recorded so far.
    pub fn steps(&self) -> Vec<Step> {
        self.steps.lock().unwrap().clone()
    }

    fn record(&self, kind: StepKind, graph: &ExecutionGraph) {
        self.steps.lock().unwrap().push(Step {
            kind,
            graph: graph.clone(),
        });
    }
}

impl Observer for RecordingObserver {
    fn on_event_added(&self, g: &ExecutionGraph, e: EventId) {
        self.record(StepKind::EventAdded { e }, g);
    }
    fn on_rf_choice(&self, g: &ExecutionGraph, r: EventId, src: Option<EventId>) {
        self.record(StepKind::RfChoice { r, src }, g);
    }
    fn on_inconsistent(&self, g: &ExecutionGraph) {
        self.record(StepKind::Inconsistent, g);
    }
    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        deleted: &BTreeSet<EventId>,
    ) {
        let deleted = deleted.iter().copied().collect();
        self.record(StepKind::BackwardRevisit { r, s, deleted }, g);
    }
    fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
        self.record(StepKind::RevisitRejected { r, s }, g);
    }
    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        self.record(StepKind::Execution { kind }, exec.graph());
    }
    fn on_execution_filtered(&self, exec: &Execution, kind: ExecutionKind) {
        self.record(StepKind::ExecutionFiltered { kind }, exec.graph());
    }
    fn on_thread_blocked(&self, g: &ExecutionGraph, tid: Tid) {
        self.record(StepKind::ThreadBlocked { tid }, g);
    }
}

/// Keeps the terminal executions grouped by outcome. Pass one to `explore` when you want
/// the graphs, canonical keys or pending sends of each outcome, not just how many there
/// were.
///
/// Under a parallel run the executions are collected in a nondeterministic order (the
/// counts are still exact); compare canonical-key *sets*, not their order.
#[derive(Debug, Default)]
pub struct ExecutionCollector {
    inner: Mutex<Collected>,
}

#[derive(Debug, Default)]
struct Collected {
    full: Vec<Execution>,
    blocked: Vec<Execution>,
    errors: Vec<Execution>,
    filtered: Vec<(Execution, ExecutionKind)>,
}

impl ExecutionCollector {
    pub fn new() -> Self {
        Self::default()
    }

    /// The full executions collected so far.
    pub fn full(&self) -> Vec<Execution> {
        self.inner.lock().unwrap().full.clone()
    }
    /// The blocked executions (maximal consistent prefixes).
    pub fn blocked(&self) -> Vec<Execution> {
        self.inner.lock().unwrap().blocked.clone()
    }
    /// The erroneous executions.
    pub fn errors(&self) -> Vec<Execution> {
        self.inner.lock().unwrap().errors.clone()
    }
    /// The terminals suppressed by the eager time filter, each paired with its kind.
    pub fn filtered(&self) -> Vec<(Execution, ExecutionKind)> {
        self.inner.lock().unwrap().filtered.clone()
    }
    /// Full followed by blocked - the terminal executions over which Theorem 4.1 forbids
    /// duplicates.
    pub fn terminals(&self) -> Vec<Execution> {
        let c = self.inner.lock().unwrap();
        c.full.iter().chain(c.blocked.iter()).cloned().collect()
    }

    pub fn full_count(&self) -> usize {
        self.inner.lock().unwrap().full.len()
    }
    pub fn blocked_count(&self) -> usize {
        self.inner.lock().unwrap().blocked.len()
    }
    pub fn error_count(&self) -> usize {
        self.inner.lock().unwrap().errors.len()
    }
    /// How many terminals the eager time filter suppressed.
    pub fn filtered_count(&self) -> usize {
        self.inner.lock().unwrap().filtered.len()
    }
    /// Full + blocked, the terminal count.
    pub fn terminal_count(&self) -> usize {
        let c = self.inner.lock().unwrap();
        c.full.len() + c.blocked.len()
    }

    /// Canonical keys of the full executions.
    pub fn full_keys(&self) -> Vec<String> {
        self.inner
            .lock()
            .unwrap()
            .full
            .iter()
            .map(Execution::canonical_key)
            .collect()
    }
    /// Canonical keys over full plus blocked, for the duplicate check.
    pub fn terminal_keys(&self) -> Vec<String> {
        let c = self.inner.lock().unwrap();
        c.full
            .iter()
            .chain(c.blocked.iter())
            .map(Execution::canonical_key)
            .collect()
    }
    /// Canonical keys of the erroneous executions.
    pub fn error_keys(&self) -> Vec<String> {
        self.inner
            .lock()
            .unwrap()
            .errors
            .iter()
            .map(Execution::canonical_key)
            .collect()
    }
    /// Canonical keys of the time-filtered terminals, sorted so the set is deterministic
    /// regardless of the (possibly parallel) collection order.
    pub fn filtered_keys(&self) -> Vec<String> {
        let mut keys: Vec<String> = self
            .inner
            .lock()
            .unwrap()
            .filtered
            .iter()
            .map(|(e, _)| e.canonical_key())
            .collect();
        keys.sort();
        keys
    }
}

impl Observer for ExecutionCollector {
    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        let mut c = self.inner.lock().unwrap();
        match kind {
            ExecutionKind::Full => c.full.push(exec.clone()),
            ExecutionKind::Blocked => c.blocked.push(exec.clone()),
            ExecutionKind::Error => c.errors.push(exec.clone()),
        }
    }
    fn on_execution_filtered(&self, exec: &Execution, kind: ExecutionKind) {
        self.inner
            .lock()
            .unwrap()
            .filtered
            .push((exec.clone(), kind));
    }
}

/// Compose two observers: every callback fans out to both, `A` before `B`.
impl<A: Observer, B: Observer> Observer for (A, B) {
    fn on_event_added(&self, g: &ExecutionGraph, e: EventId) {
        self.0.on_event_added(g, e);
        self.1.on_event_added(g, e);
    }
    fn on_rf_choice(&self, g: &ExecutionGraph, r: EventId, src: Option<EventId>) {
        self.0.on_rf_choice(g, r, src);
        self.1.on_rf_choice(g, r, src);
    }
    fn on_inconsistent(&self, g: &ExecutionGraph) {
        self.0.on_inconsistent(g);
        self.1.on_inconsistent(g);
    }
    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        deleted: &BTreeSet<EventId>,
    ) {
        self.0.on_backward_revisit(g, r, s, deleted);
        self.1.on_backward_revisit(g, r, s, deleted);
    }
    fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
        self.0.on_revisit_rejected(g, r, s);
        self.1.on_revisit_rejected(g, r, s);
    }
    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        self.0.on_execution(exec, kind);
        self.1.on_execution(exec, kind);
    }
    fn on_execution_filtered(&self, exec: &Execution, kind: ExecutionKind) {
        self.0.on_execution_filtered(exec, kind);
        self.1.on_execution_filtered(exec, kind);
    }
    fn on_thread_blocked(&self, g: &ExecutionGraph, tid: Tid) {
        self.0.on_thread_blocked(g, tid);
        self.1.on_thread_blocked(g, tid);
    }
}
