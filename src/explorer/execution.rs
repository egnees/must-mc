//! A completed execution.
//!
//! An [`Execution`] wraps a final execution graph. `explore` hands one to the [`Observer`]
//! at every terminal outcome ([`ExecutionKind`]); the observer decides what to keep. To
//! hold on to the executions themselves - their graphs, canonical keys, pending sends -
//! pass an observer that records them, such as the crate's [`ExecutionCollector`].
//!
//! [`Observer`]: crate::observer::Observer
//! [`ExecutionCollector`]: crate::observer::ExecutionCollector

use crate::event::EventId;
use crate::graph::ExecutionGraph;

/// How an explored execution terminated.
///
/// * `Full` - nothing more can be added and every thread finished.
/// * `Blocked` - nothing more can be added but some thread is stuck on a blocking receive
///   that never got a message (a maximal consistent prefix).
/// * `Error` - an `error` event was reached.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExecutionKind {
    Full,
    Blocked,
    Error,
}

/// A completed execution: the final graph plus cheap read-only queries over it.
#[derive(Clone, Debug)]
pub struct Execution {
    graph: ExecutionGraph,
}

impl Execution {
    pub fn new(graph: ExecutionGraph) -> Self {
        Execution { graph }
    }

    pub fn graph(&self) -> &ExecutionGraph {
        &self.graph
    }

    /// Pending (unread) sends `G.US` - a hook for reasoning about undelivered messages.
    pub fn pending_sends(&self) -> Vec<EventId> {
        self.graph.unread_sends()
    }

    /// Canonical `(E, po, rf)` key, ignoring insertion order - the key behind the "no
    /// duplicate executions" guarantee.
    pub fn canonical_key(&self) -> String {
        self.graph.canonical_key()
    }
}
