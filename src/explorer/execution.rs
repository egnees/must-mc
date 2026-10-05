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
use crate::program::TraceLabel;

/// How an explored execution terminated.
///
/// * `Full` - `next_P(G) = nothing` with every thread finished (line 4).
/// * `Blocked` - `next_P(G) = nothing` with some thread stuck on a blocking receive that
///   never got a message (a maximal consistent prefix).
/// * `Error` - an `error` event was reached (line 5).
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
    labels: Vec<TraceLabel>,
}

impl Execution {
    pub fn new(graph: ExecutionGraph) -> Self {
        Execution {
            graph,
            labels: Vec::new(),
        }
    }

    pub(crate) fn with_labels(mut self, labels: Vec<TraceLabel>) -> Self {
        self.labels = labels;
        self
    }

    pub fn graph(&self) -> &ExecutionGraph {
        &self.graph
    }

    /// Local annotations, ordered by thread and insertion order within each thread.
    /// They do not participate in graph identity or timing. For early error prefixes,
    /// see [`Program::labels`](crate::Program::labels) for the prefix semantics.
    pub fn labels(&self) -> &[TraceLabel] {
        &self.labels
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
