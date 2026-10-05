//! The boundary between the runtime and the explorer.
//!
//! A `Program` is the pure, declarative view the explorer sees: given the values each
//! thread's events have already produced, it reports the next event of every thread (or
//! that the thread has finished). The runtime implements this by replaying stackless
//! coroutines; table-driven mock programs implement it directly to test the explorer
//! without coroutines.
//!
//! ## The `traces` contract
//!
//! `traces[i]` holds **one value per already-committed event of thread `i`**, in program
//! order (po) - exactly the paper's `trace_G(i) = (G.val(e_1), ..., G.val(e_n))`, where
//! `n` is the number of thread-`i` events. Each entry is:
//!   * `Some(v)` - a **receive** that read value `v` from some send;
//!   * `None` - a **send** or **error** event (whose value is nothing), or a receive
//!     that read nothing (a timeout or a non-blocking receive).
//!
//! So `traces[i].len()` is the number of thread-`i` events already in the graph, and
//! `next(traces)[i]` is the `(len + 1)`-th event - the paper's `P_i(trace) = e_{n+1}`.
//!
//! Why a value per *event* and not per receive: after the explorer adds a send between
//! two receives and re-calls `next`, a receive-only trace would be unchanged, so `next`
//! could not tell which send comes next. Carrying a value per event (with `None` for a
//! send) restores the bijection between trace position and po position and keeps `next` a
//! pure function of `traces`. The runtime tells a send-`None` from a receive-`None`
//! structurally - it re-executes the body and knows the k-th API call - never from the
//! entry's shape.
//!
//! ### How the explorer drives a thread event by event
//!
//! The explorer adds events one at a time and, after **every** added event of thread
//! `i`, appends one entry to `traces[i]` (`None` for a send or error, `Some(v)` or
//! `None` for a receive it just resolved), then calls `next` again. Because the trace
//! grows by one per event, `next` advances to the following event each time - this is
//! what lets several sends between two receives be enumerated one by one.
//!
//! To build `traces[i]` from a graph `G`: walk thread `i`'s events in po; push
//! `Some(val(rf(e)))` for a receive that reads a send, and `None` for a receive that
//! read nothing and for every send or error.
//!
//! The runtime guarantees determinism: identical `traces` yield identical labels.
//! Process bodies must be pure functions of the values they receive - no clocks, IO, or
//! randomness.

use crate::event::{Label, Tid, Val};

/// The next step of a single thread under a given trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThreadNext {
    /// The thread's next event: the send, receive, or error that follows its
    /// already-resolved events in po.
    Next(Label),
    /// The thread has no next event under this trace.
    Finished,
}

impl ThreadNext {
    pub fn is_finished(&self) -> bool {
        matches!(self, ThreadNext::Finished)
    }
    pub fn label(&self) -> Option<&Label> {
        match self {
            ThreadNext::Next(l) => Some(l),
            ThreadNext::Finished => None,
        }
    }
}

/// A program as seen by the explorer: a total, deterministic function from per-thread
/// traces to per-thread next events.
pub trait Program {
    /// Number of threads `N`; thread ids are `0..N`.
    fn num_threads(&self) -> usize;

    /// The next event of every thread under `traces`. The returned vector has length
    /// `num_threads()`; index `i` is thread `i`'s [`ThreadNext`]. `traces` must also have
    /// length `num_threads()` - one per-event trace per thread (see the module docs for
    /// the exact contract between `traces` and events).
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext>;

    /// The next event of a *single* thread from its own trace. `next(traces)[tid]` is a
    /// pure function of `traces[tid]` (each process only sees the values it receives), so
    /// the explorer can recompute just the one thread whose trace grew.
    ///
    /// The default recomputes all threads and keeps `tid`'s answer; it is correct for any
    /// contract-abiding program. Implementations with a cheaper per-thread replay (the
    /// coroutine runtime) override it.
    fn next_thread(&self, tid: Tid, trace: &[Option<Val>]) -> ThreadNext {
        let mut traces = vec![Vec::new(); self.num_threads()];
        if let Some(slot) = traces.get_mut(tid) {
            *slot = trace.to_vec();
        }
        self.next(&traces).swap_remove(tid)
    }

    /// A **sound over-approximation** of the events thread `tid` may still produce, given
    /// its trace so far — the labels that can appear at this po-position or later in *some*
    /// continuation.
    ///
    /// The contract: if this returns `Some(labels)`, then in *every* continuation of `trace`,
    /// each of thread `tid`'s future events (its next one and all after it) is **represented**
    /// in `labels`. "Represented" is not label equality — it is what the two consumers actually
    /// test ([`crate::time::force_source`] conditions (2) and (3b)):
    ///
    /// * a future **send** must be represented by some `Label::Send` with the same `dst` and the
    ///   same payload. Its `model` and delivery `window` are never inspected, so they may be
    ///   approximate;
    /// * a future **receive** must be represented by some `Label::Recv` whose predicate accepts a
    ///   **superset** of the payloads that receive can accept (`Pred::any()` always works). Its
    ///   `blocking` flag is *not* inspected either — a declared blocking receive covers a real
    ///   non-blocking one and vice versa — so when in doubt, declare one wide receive;
    /// * nondet and error events are never inspected; listing them is harmless, omitting them
    ///   costs nothing today. (Do not rely on that: a future consumer may look.)
    ///
    /// `None` means "unknown" — the caller must assume any event is possible.
    ///
    /// The forced-closure gate ([`crate::time::forced_closure`]) uses this for **C1
    /// soundness**: it forces a blocking receive `r ← S` only when `S` is statically the
    /// *only* source `r` could ever read *and* `r` is the only receive that could ever
    /// consume `S` — both proved via this over-approximation of every thread's future. A
    /// wrong (too-narrow) answer would over-prune and lose realizable terminals, so the
    /// default is the safe `None`: a program with value-dependent control flow (the
    /// coroutine runtime) is C1-safe with no analysis, at the cost of forcing fewer
    /// receives (never fewer than sound).
    ///
    /// # Position 0 is the *next* event
    ///
    /// The one positional requirement: when the thread has a next event (`next_thread` is
    /// `Next(l)`), `labels[0]` must be exactly `l`. Everything after index 0 over-approximates
    /// the events strictly after it. `force_source` needs this to separate the receive it is
    /// forcing from the *other* receives that might consume the same message (condition (3b));
    /// without it, a thread whose alphabet contains its own receive could never be forced.
    /// Beyond index 0 the order is unconstrained — the caller only tests membership. A
    /// `Finished` thread may answer `Some(vec![])`, its exact future.
    fn possible_future(&self, _tid: Tid, _trace: &[Option<Val>]) -> Option<Vec<Label>> {
        None
    }
}
