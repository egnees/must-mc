//! Stable total orders for MUST's untimed canonical receive source.
//!
//! Ordering never removes an untimed-consistent candidate. The selector must depend
//! only on the graph with the queried receive's incoming RF erased, not its current
//! choice or insertion stamps. Both orders below use only a source's identity/label.

use crate::{EventId, ExecutionGraph};

/// How to choose among all untimed-consistent sources in canonical completion.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SourceOrder {
    /// Original MUST implementation order: thread ID, then local event index.
    #[default]
    EventId,
    /// Prefer messages sent to the sender itself, then use original EventId order.
    /// Self-messages often represent timers, giving them a stable canonical position.
    /// This changes the construction tree without filtering any candidate by timing.
    SelfSendFirst,
}

impl SourceOrder {
    pub(crate) fn key(self, g: &ExecutionGraph, source: EventId) -> (bool, EventId) {
        let remote = self == Self::SelfSendFirst && g.label(source).dst() != Some(source.tid);
        (remote, source)
    }
}
