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

use crate::event::{EventId, Label, Tid, Val};
use crate::explorer::{Execution, ExecutionKind};
use crate::graph::ExecutionGraph;

/// Outcome of one certificate-pruning attempt. Only `Pruned` changes exploration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TimeCertificateOutcome {
    CompletionUnknown,
    CompletionWitness,
    OwnershipUnknown,
    Pruned,
}

/// Diagnostic cost of semantic lookahead and construction-coverage checking.
/// Counts include proof work that was inconclusive. They are separate from main Visits
/// and reported executions; proof search never invokes execution callbacks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimeCertificateEvent {
    pub outcome: TimeCertificateOutcome,
    pub completion_states: usize,
    pub completion_events: usize,
    pub completion_cases: usize,
    pub completion_temporal_checks: usize,
    pub ownership_states: usize,
    pub ownership_events: usize,
    pub ownership_temporal_checks: usize,
    pub revisit_candidates: usize,
    pub canonical_checks: usize,
}

/// Result of checking the immutable part of an original-MUST construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrozenTimeOutcome {
    /// The graph is outside the supported Asyn/P2p fragment.
    Unsupported,
    /// No contradiction was certified; ordinary exploration continues.
    Feasible,
    /// An immutable-core or first-alteration sender certificate rejects the subtree.
    Pruned,
}

/// Cost of one immutable-core and first-alteration sender check. Separate from future-completion and
/// no-escape proof walks. A solver call is a query, not one internal solver step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrozenTimeEvent {
    pub outcome: FrozenTimeOutcome,
    pub cache_hit: bool,
    pub solver_calls: usize,
    /// Number of immutable events in this query's core.
    pub core_events: usize,
    /// Deterministic effects appended to the proof graph, never to the search graph.
    pub mandatory_events: usize,
    /// Full untimed consistency trials used to establish blocking-receive anchors.
    pub blocker_trials: usize,
    pub program_steps: usize,
    /// Attempts to refute every possible sender of a first change to the old graph.
    pub source_checks: usize,
    /// Subset of Pruned outcomes certified by the first-alteration sender rule.
    pub source_prunes: usize,
    /// Temporal queries for the old graph and sender causal cores.
    pub source_solver_calls: usize,
    /// Sum of event counts across those temporal query graphs.
    pub source_core_events: usize,
    /// Program calls to determine which old thread traces have finished.
    pub source_program_steps: usize,
    /// Unfinished sender obligations inspected; no future execution states are enumerated.
    pub source_tails: usize,
    /// Sound future-alphabet queries used to exclude processes that cannot send.
    pub source_future_queries: usize,
}

/// Callbacks fired by the explorer. Every method defaults to a no-op.
pub trait Observer {
    /// Whether event-added notifications may be replaced by a final count.
    /// Opt in only if event graphs, identities, ordering and intermediate counts
    /// are unused. The explorer then flushes once on worker exit (also on unwind).
    fn allows_buffered_events(&self) -> bool {
        false
    }
    /// Final added-event count from one explorer worker. Opt-in implementations
    /// must count it without panicking, including when called during unwinding.
    fn on_events_added_batch(&self, _count: usize) {}
    /// Whether structurally rejected RF trials contribute observable callbacks.
    ///
    /// Return `false` only when `on_rf_choice` and `on_inconsistent` ignore trials
    /// whose source has the wrong destination or is already consumed. Those
    /// universally inconsistent trials may then be omitted entirely. This is
    /// stronger than ignoring their graph: metadata-counting observers must
    /// retain the conservative default. Other source checks and bottom remain.
    fn observes_rejected_rf_trials(&self) -> bool {
        true
    }

    /// Whether RF-choice and inconsistency callbacks inspect or retain their graph.
    ///
    /// The conservative default preserves fully materialized trial graphs. Return
    /// `false` only when both [`Self::on_rf_choice`] and [`Self::on_inconsistent`]
    /// ignore the graph argument: rejected choices may then report their metadata
    /// against a preceding trial or host graph, without storing the rejected RF
    /// edge. Callback order and counts remain unchanged; accepted RF choices
    /// still receive their actual graph.
    fn inspects_rf_trial_graphs(&self) -> bool {
        true
    }

    /// Whether candidate/arm-rejection callbacks inspect or retain their target graph.
    /// Return `false` only when [`Self::on_revisit_candidate`] and
    /// [`Self::on_revisit_arm_rejected`] ignore their `target` argument. Untimed
    /// Asyn trials may then provide the host graph in its place and materialize
    /// the target only when canonical checks accept the revisit. Their host graph,
    /// event metadata, callback order and counts remain unchanged.
    fn inspects_revisit_targets(&self) -> bool {
        true
    }

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
    /// A backward-revisit target passed consistency and any enabled time gate, and its
    /// canonical arms are about to be checked. `g` is the send-add host; `target` is the
    /// restricted graph with `r` redirected to `s`. Diagnostic-only, with no graph cloning
    /// or extra oracle work unless the observer requests it.
    fn on_revisit_candidate(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _target: &ExecutionGraph,
    ) {
    }
    /// A canonical condition rejected the candidate. For ordinary arms, this identifies
    /// the first false arm; preceding oracle callbacks identify any smaller viable
    /// alternative. A certified-owner rejection first emits `on_revisit_owner_certified`
    /// and reports the victim receive here. Other arms can reject for structural or
    /// candidate-membership reasons.
    fn on_revisit_arm_rejected(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _target: &ExecutionGraph,
        _event: EventId,
    ) {
    }
    /// An alternate canonical owner was certified by replay from the root. `owner` has
    /// the exact insertion order required to produce the same restricted target state.
    /// This certificate rejects the current redundant backward edge; it is not a general
    /// completeness certificate for T2. `replay_events` is the number of replayed events.
    fn on_revisit_owner_certified(
        &self,
        _g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        _owner: &ExecutionGraph,
        _replay_events: usize,
    ) {
    }
    /// A backward revisit setting `rf(r)` to `s` was pruned by the eager-time forced-closure
    /// gate. This check runs before the canonical arms, so it does not imply they passed.
    /// A diagnostic hook only — it does not change any count.
    fn on_forced_closure_pruned(&self, _g: &ExecutionGraph, _r: EventId, _s: EventId) {}
    /// The nondet-arm existential canon oracle ([`crate::time::viable`], T2_ORACLE_SPEC §1.1)
    /// returned `verdict` for re-pinning `ep` to `v` in `base` while testing the revisit by the
    /// send `revisiting` (labelled `rev_label`). Fires once per oracle call — only for values
    /// strictly below the held one, i.e. only when a non-min holder is under test (a min holder
    /// makes no calls). Diagnostic-only: the T-DIFF harness cross-checks every verdict against
    /// a brute-force reference (O2), and the canon logger mines these for regression seeds
    /// (§3.3). Never affects counts.
    #[allow(clippy::too_many_arguments)]
    fn on_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _v: Val,
        _revisiting: EventId,
        _rev_label: &Label,
        _verdict: bool,
    ) {
    }
    /// Debug-only held-value query for a nonminimum nondeterministic canonical arm.
    /// Unlike `on_viable_verdict`, this is a diagnostic, not a smaller alternative used
    /// to reject a holder. A false answer is possible on an infeasible send-add host or
    /// a candidate later rejected by another arm; it must not abort the main search.
    fn on_held_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _value: Val,
        _revisiting: EventId,
        _rev_label: &Label,
        _verdict: bool,
    ) {
    }
    /// The blocking-receive twin of [`on_viable_verdict`](Self::on_viable_verdict): the R1 canon
    /// oracle ([`crate::time::viable_recv`], `C1_HARDENING_SPEC` §D.5) returned `verdict` for
    /// re-pinning `rf(ep)` to `src`. Fires only for candidates strictly `≺`-below the held
    /// source, so a min-holder makes no calls. Diagnostic-only; never affects counts.
    #[allow(clippy::too_many_arguments)]
    fn on_viable_recv_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _src: EventId,
        _revisiting: EventId,
        _rev_label: &Label,
        _verdict: bool,
    ) {
    }
    /// A Visit node `Visit_P(G)` is being entered (once per `visit_step` call). Paired with
    /// [`on_visit_exit`](Self::on_visit_exit). The dead-branch detector (T2_PLAN §5а) uses this
    /// to count examined nodes, including certificate-cut boundaries, and via
    /// `on_visit_exit`'s flag those whose subtree bore no accepted terminal.
    fn on_visit_enter(&self, _g: &ExecutionGraph) {}
    /// The Visit node entered with [`on_visit_enter`](Self::on_visit_enter) is done;
    /// `produced_terminal` is whether its subtree reported at least one terminal. Reliable only
    /// on the sequential path (a donated subtree records on another worker), which is where the
    /// dead-branch detector runs.
    fn on_visit_exit(&self, _g: &ExecutionGraph, _produced_terminal: bool) {}
    /// Certificate check before expanding a main Visit. `Pruned` means both semantic
    /// impossibility and absence of escaping canonical revisits were certified.
    fn on_time_certificate(&self, _g: &ExecutionGraph, _event: &TimeCertificateEvent) {}
    /// Immutable-core timing check before expanding a main Visit. A pruning result
    /// preserves every time-valid terminal of original MUST. It either refutes an
    /// obligatory core or every possible first repairing sender. Mandatory effects
    /// need only occur in terminal completions, not every prefix.
    fn on_frozen_time(&self, _g: &ExecutionGraph, _event: &FrozenTimeEvent) {}
    /// A terminal execution (full / blocked / error) was reached.
    fn on_execution(&self, _exec: &Execution, _kind: ExecutionKind) {}
    /// Construction stopped before another send would exceed `Config::max_sends`.
    /// `g` is the prefix before that send, not a completed execution or a proven
    /// counterexample. Any such callback makes the search incomplete; even executions
    /// within the budget may require an over-budget construction and a backward revisit.
    /// This callback is not subject to terminal timing filters.
    fn on_send_limit(&self, _g: &ExecutionGraph, _limit: usize) {}
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

impl Observer for NullObserver {
    fn allows_buffered_events(&self) -> bool {
        true
    }
    fn observes_rejected_rf_trials(&self) -> bool {
        false
    }
    fn inspects_rf_trial_graphs(&self) -> bool {
        false
    }
    fn inspects_revisit_targets(&self) -> bool {
        false
    }
}

// 128-byte padding also separates adjacent worker counters on Apple CPUs with
// 128-byte cache lines; on 64-byte-line CPUs the extra padding is conservative.
#[repr(align(128))]
#[derive(Debug, Default)]
struct EventShard {
    events_added: AtomicUsize,
    full: AtomicUsize,
    blocked: AtomicUsize,
    errors: AtomicUsize,
}

/// Counts added events and reported terminal outcomes, leaving trial diagnostics
/// disabled. Shards use atomic counters even when several workers share a shard.
#[derive(Debug)]
pub struct EventCountingObserver {
    shards: Vec<EventShard>,
    buffered_events: bool,
}

impl Default for EventCountingObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl EventCountingObserver {
    pub fn new() -> Self {
        Self::with_shards(default_shards())
    }
    /// Use at least one shard; collisions remain safe through atomic increments.
    pub fn with_shards(shards: usize) -> Self {
        Self {
            shards: (0..shards.max(1)).map(|_| EventShard::default()).collect(),
            buffered_events: false,
        }
    }
    /// Count added events locally in each explorer worker and flush on exit.
    /// `events_added()` may lag throughout a run, including inside execution
    /// callbacks; it is complete after `explore` returns. Terminal counts keep
    /// their usual immediate behavior. Conservative tuple partners retain the
    /// ordinary per-event notifications.
    pub fn with_buffered_events(mut self) -> Self {
        self.buffered_events = true;
        self
    }
    fn shard(&self) -> &EventShard {
        &self.shards[worker_id() % self.shards.len()]
    }
    fn total(&self, pick: impl Fn(&EventShard) -> &AtomicUsize) -> usize {
        self.shards
            .iter()
            .map(|s| pick(s).load(Ordering::Relaxed))
            .sum()
    }
    pub fn events_added(&self) -> usize {
        self.total(|s| &s.events_added)
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
    pub fn terminal(&self) -> usize {
        self.full() + self.blocked()
    }
}

impl Observer for EventCountingObserver {
    fn allows_buffered_events(&self) -> bool {
        self.buffered_events
    }
    fn on_events_added_batch(&self, count: usize) {
        self.shard()
            .events_added
            .fetch_add(count, Ordering::Relaxed);
    }
    fn observes_rejected_rf_trials(&self) -> bool {
        false
    }
    fn inspects_rf_trial_graphs(&self) -> bool {
        false
    }
    fn inspects_revisit_targets(&self) -> bool {
        false
    }
    fn on_event_added(&self, _g: &ExecutionGraph, _e: EventId) {
        self.shard().events_added.fetch_add(1, Ordering::Relaxed);
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
}

/// One worker's tallies. 128-byte alignment separates adjacent shards even on
/// CPUs with 128-byte cache lines. Atomics also keep shard collisions safe.
#[repr(align(128))]
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
    send_limit_hits: AtomicUsize,
    filtered_full: AtomicUsize,
    filtered_blocked: AtomicUsize,
    filtered_errors: AtomicUsize,
    threads_blocked: AtomicUsize,
    time_certificate_checks: AtomicUsize,
    time_certificate_prunes: AtomicUsize,
    time_certificate_unknown: AtomicUsize,
    time_completion_states: AtomicUsize,
    time_completion_events: AtomicUsize,
    time_completion_cases: AtomicUsize,
    time_ownership_states: AtomicUsize,
    time_ownership_events: AtomicUsize,
    time_revisit_candidates: AtomicUsize,
    time_canonical_checks: AtomicUsize,
    time_proof_temporal_checks: AtomicUsize,
    frozen_checks: AtomicUsize,
    frozen_prunes: AtomicUsize,
    frozen_unsupported: AtomicUsize,
    frozen_cache_hits: AtomicUsize,
    frozen_solver_calls: AtomicUsize,
    frozen_core_events: AtomicUsize,
    frozen_mandatory_events: AtomicUsize,
    frozen_blocker_trials: AtomicUsize,
    frozen_program_steps: AtomicUsize,
    frozen_source_checks: AtomicUsize,
    frozen_source_prunes: AtomicUsize,
    frozen_source_solver_calls: AtomicUsize,
    frozen_source_core_events: AtomicUsize,
    frozen_source_program_steps: AtomicUsize,
    frozen_source_tails: AtomicUsize,
    frozen_source_future_queries: AtomicUsize,
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
    /// Inconclusive construction cutoffs, separate from all terminal counts.
    /// Any nonzero value means absence of errors is not a complete verification.
    pub fn send_limit_hits(&self) -> usize {
        self.total(|s| &s.send_limit_hits)
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

    pub fn time_certificate_checks(&self) -> usize {
        self.total(|s| &s.time_certificate_checks) + self.frozen_checks()
    }
    pub fn time_certificate_prunes(&self) -> usize {
        self.total(|s| &s.time_certificate_prunes) + self.frozen_prunes()
    }
    pub fn time_certificate_unknown(&self) -> usize {
        self.total(|s| &s.time_certificate_unknown) + self.frozen_unsupported()
    }
    pub fn time_completion_states(&self) -> usize {
        self.total(|s| &s.time_completion_states)
    }
    pub fn time_completion_events(&self) -> usize {
        self.total(|s| &s.time_completion_events)
    }
    pub fn time_completion_cases(&self) -> usize {
        self.total(|s| &s.time_completion_cases)
    }
    pub fn time_ownership_states(&self) -> usize {
        self.total(|s| &s.time_ownership_states)
    }
    pub fn time_ownership_events(&self) -> usize {
        self.total(|s| &s.time_ownership_events)
    }
    pub fn time_revisit_candidates(&self) -> usize {
        self.total(|s| &s.time_revisit_candidates)
    }
    pub fn time_canonical_checks(&self) -> usize {
        self.total(|s| &s.time_canonical_checks)
    }
    /// Temporal feasibility queries in both proof layers, including unsuccessful attempts.
    /// This counts queries, not the internal work of the disjunctive solver.
    pub fn time_proof_temporal_checks(&self) -> usize {
        self.total(|s| &s.time_proof_temporal_checks)
            + self.frozen_solver_calls()
            + self.frozen_source_solver_calls()
    }

    pub fn frozen_checks(&self) -> usize {
        self.total(|s| &s.frozen_checks)
    }
    pub fn frozen_prunes(&self) -> usize {
        self.total(|s| &s.frozen_prunes)
    }
    pub fn frozen_unsupported(&self) -> usize {
        self.total(|s| &s.frozen_unsupported)
    }
    pub fn frozen_cache_hits(&self) -> usize {
        self.total(|s| &s.frozen_cache_hits)
    }
    pub fn frozen_solver_calls(&self) -> usize {
        self.total(|s| &s.frozen_solver_calls)
    }
    /// Sum of core sizes at actual solver queries, excluding cache hits.
    pub fn frozen_core_events(&self) -> usize {
        self.total(|s| &s.frozen_core_events)
    }
    pub fn frozen_mandatory_events(&self) -> usize {
        self.total(|s| &s.frozen_mandatory_events)
    }
    pub fn frozen_blocker_trials(&self) -> usize {
        self.total(|s| &s.frozen_blocker_trials)
    }
    pub fn frozen_program_steps(&self) -> usize {
        self.total(|s| &s.frozen_program_steps)
    }

    pub fn frozen_source_checks(&self) -> usize {
        self.total(|s| &s.frozen_source_checks)
    }
    pub fn frozen_source_prunes(&self) -> usize {
        self.total(|s| &s.frozen_source_prunes)
    }
    pub fn frozen_source_solver_calls(&self) -> usize {
        self.total(|s| &s.frozen_source_solver_calls)
    }
    pub fn frozen_source_core_events(&self) -> usize {
        self.total(|s| &s.frozen_source_core_events)
    }
    pub fn frozen_source_program_steps(&self) -> usize {
        self.total(|s| &s.frozen_source_program_steps)
    }
    pub fn frozen_source_tails(&self) -> usize {
        self.total(|s| &s.frozen_source_tails)
    }

    pub fn frozen_source_future_queries(&self) -> usize {
        self.total(|s| &s.frozen_source_future_queries)
    }

    /// Total terminal executions (full + blocked).
    pub fn terminal(&self) -> usize {
        self.full() + self.blocked()
    }
}

impl Observer for CountingObserver {
    fn inspects_rf_trial_graphs(&self) -> bool {
        false
    }
    fn inspects_revisit_targets(&self) -> bool {
        false
    }
    fn on_frozen_time(&self, _g: &ExecutionGraph, event: &FrozenTimeEvent) {
        let shard = self.shard();
        shard.frozen_checks.fetch_add(1, Ordering::Relaxed);
        match event.outcome {
            FrozenTimeOutcome::Pruned => {
                shard.frozen_prunes.fetch_add(1, Ordering::Relaxed);
            }
            FrozenTimeOutcome::Unsupported => {
                shard.frozen_unsupported.fetch_add(1, Ordering::Relaxed);
            }
            FrozenTimeOutcome::Feasible => {}
        }
        shard
            .frozen_cache_hits
            .fetch_add(usize::from(event.cache_hit), Ordering::Relaxed);
        shard
            .frozen_solver_calls
            .fetch_add(event.solver_calls, Ordering::Relaxed);
        if event.solver_calls != 0 {
            shard
                .frozen_core_events
                .fetch_add(event.core_events, Ordering::Relaxed);
        }
        shard
            .frozen_mandatory_events
            .fetch_add(event.mandatory_events, Ordering::Relaxed);
        shard
            .frozen_blocker_trials
            .fetch_add(event.blocker_trials, Ordering::Relaxed);
        shard
            .frozen_program_steps
            .fetch_add(event.program_steps, Ordering::Relaxed);
        shard
            .frozen_source_checks
            .fetch_add(event.source_checks, Ordering::Relaxed);
        shard
            .frozen_source_prunes
            .fetch_add(event.source_prunes, Ordering::Relaxed);
        shard
            .frozen_source_solver_calls
            .fetch_add(event.source_solver_calls, Ordering::Relaxed);
        shard
            .frozen_source_core_events
            .fetch_add(event.source_core_events, Ordering::Relaxed);
        shard
            .frozen_source_program_steps
            .fetch_add(event.source_program_steps, Ordering::Relaxed);
        shard
            .frozen_source_tails
            .fetch_add(event.source_tails, Ordering::Relaxed);
        shard
            .frozen_source_future_queries
            .fetch_add(event.source_future_queries, Ordering::Relaxed);
    }
    fn on_time_certificate(&self, _g: &ExecutionGraph, event: &TimeCertificateEvent) {
        let shard = self.shard();
        shard
            .time_certificate_checks
            .fetch_add(1, Ordering::Relaxed);
        match event.outcome {
            TimeCertificateOutcome::Pruned => {
                shard
                    .time_certificate_prunes
                    .fetch_add(1, Ordering::Relaxed);
            }
            TimeCertificateOutcome::CompletionUnknown
            | TimeCertificateOutcome::OwnershipUnknown => {
                shard
                    .time_certificate_unknown
                    .fetch_add(1, Ordering::Relaxed);
            }
            TimeCertificateOutcome::CompletionWitness => {}
        }
        shard
            .time_completion_states
            .fetch_add(event.completion_states, Ordering::Relaxed);
        shard
            .time_completion_events
            .fetch_add(event.completion_events, Ordering::Relaxed);
        shard
            .time_completion_cases
            .fetch_add(event.completion_cases, Ordering::Relaxed);
        shard
            .time_ownership_states
            .fetch_add(event.ownership_states, Ordering::Relaxed);
        shard
            .time_ownership_events
            .fetch_add(event.ownership_events, Ordering::Relaxed);
        shard
            .time_revisit_candidates
            .fetch_add(event.revisit_candidates, Ordering::Relaxed);
        shard
            .time_canonical_checks
            .fetch_add(event.canonical_checks, Ordering::Relaxed);
        shard.time_proof_temporal_checks.fetch_add(
            event.completion_temporal_checks + event.ownership_temporal_checks,
            Ordering::Relaxed,
        );
    }
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
    fn on_send_limit(&self, _g: &ExecutionGraph, _limit: usize) {
        self.shard().send_limit_hits.fetch_add(1, Ordering::Relaxed);
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

/// Counts every examined Visit, including certificate-pruned boundaries, and those whose
/// explored subtree produced **no accepted terminal**. The latter is the measured barren
/// work of that construction, not a claim that the graph has no semantic continuation.
/// Solver alternatives and temporary proof graphs are separate work, not Visit nodes.
///
/// Sequential runs only: `on_visit_exit`'s `produced_terminal` is unreliable under parallelism
/// (a donated subtree records on another worker), so use a single thread.
#[derive(Debug, Default)]
pub struct DeadBranchDetector {
    visits: AtomicUsize,
    dead: AtomicUsize,
}

impl DeadBranchDetector {
    pub fn new() -> Self {
        Self::default()
    }
    /// Total Visit nodes entered.
    pub fn visits(&self) -> usize {
        self.visits.load(Ordering::Relaxed)
    }
    /// Visit nodes whose explored subtree produced no accepted terminal.
    pub fn dead(&self) -> usize {
        self.dead.load(Ordering::Relaxed)
    }
}

impl Observer for DeadBranchDetector {
    fn on_visit_exit(&self, _g: &ExecutionGraph, produced_terminal: bool) {
        self.visits.fetch_add(1, Ordering::Relaxed);
        if !produced_terminal {
            self.dead.fetch_add(1, Ordering::Relaxed);
        }
    }
}

/// Compose two observers: every callback fans out to both, `A` before `B`.
impl<A: Observer, B: Observer> Observer for (A, B) {
    fn allows_buffered_events(&self) -> bool {
        self.0.allows_buffered_events() && self.1.allows_buffered_events()
    }
    fn on_events_added_batch(&self, count: usize) {
        self.0.on_events_added_batch(count);
        self.1.on_events_added_batch(count);
    }
    fn observes_rejected_rf_trials(&self) -> bool {
        self.0.observes_rejected_rf_trials() || self.1.observes_rejected_rf_trials()
    }
    fn inspects_rf_trial_graphs(&self) -> bool {
        self.0.inspects_rf_trial_graphs() || self.1.inspects_rf_trial_graphs()
    }
    fn inspects_revisit_targets(&self) -> bool {
        self.0.inspects_revisit_targets() || self.1.inspects_revisit_targets()
    }
    fn on_frozen_time(&self, g: &ExecutionGraph, event: &FrozenTimeEvent) {
        self.0.on_frozen_time(g, event);
        self.1.on_frozen_time(g, event);
    }
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
    fn on_revisit_candidate(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        target: &ExecutionGraph,
    ) {
        self.0.on_revisit_candidate(g, r, s, target);
        self.1.on_revisit_candidate(g, r, s, target);
    }
    fn on_revisit_arm_rejected(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        target: &ExecutionGraph,
        event: EventId,
    ) {
        self.0.on_revisit_arm_rejected(g, r, s, target, event);
        self.1.on_revisit_arm_rejected(g, r, s, target, event);
    }
    fn on_revisit_owner_certified(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        owner: &ExecutionGraph,
        replay_events: usize,
    ) {
        self.0
            .on_revisit_owner_certified(g, r, s, owner, replay_events);
        self.1
            .on_revisit_owner_certified(g, r, s, owner, replay_events);
    }
    fn on_forced_closure_pruned(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
        self.0.on_forced_closure_pruned(g, r, s);
        self.1.on_forced_closure_pruned(g, r, s);
    }
    fn on_viable_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        v: Val,
        revisiting: EventId,
        rev_label: &Label,
        verdict: bool,
    ) {
        self.0
            .on_viable_verdict(base, ep, v, revisiting, rev_label, verdict);
        self.1
            .on_viable_verdict(base, ep, v, revisiting, rev_label, verdict);
    }
    fn on_held_viable_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        value: Val,
        revisiting: EventId,
        rev_label: &Label,
        verdict: bool,
    ) {
        self.0
            .on_held_viable_verdict(base, ep, value, revisiting, rev_label, verdict);
        self.1
            .on_held_viable_verdict(base, ep, value, revisiting, rev_label, verdict);
    }
    fn on_viable_recv_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        src: EventId,
        revisiting: EventId,
        rev_label: &Label,
        verdict: bool,
    ) {
        self.0
            .on_viable_recv_verdict(base, ep, src, revisiting, rev_label, verdict);
        self.1
            .on_viable_recv_verdict(base, ep, src, revisiting, rev_label, verdict);
    }
    fn on_visit_enter(&self, g: &ExecutionGraph) {
        self.0.on_visit_enter(g);
        self.1.on_visit_enter(g);
    }
    fn on_visit_exit(&self, g: &ExecutionGraph, produced_terminal: bool) {
        self.0.on_visit_exit(g, produced_terminal);
        self.1.on_visit_exit(g, produced_terminal);
    }
    fn on_time_certificate(&self, g: &ExecutionGraph, event: &TimeCertificateEvent) {
        self.0.on_time_certificate(g, event);
        self.1.on_time_certificate(g, event);
    }
    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        self.0.on_execution(exec, kind);
        self.1.on_execution(exec, kind);
    }
    fn on_send_limit(&self, g: &ExecutionGraph, limit: usize) {
        self.0.on_send_limit(g, limit);
        self.1.on_send_limit(g, limit);
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
