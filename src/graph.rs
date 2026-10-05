//! Execution graph: events plus program order (po) and the reads-from relation (rf),
//! with an insertion order over the events.
//!
//! `po` is exactly the order of events inside a thread vector. The insertion order is
//! materialised with a per-event stamp: insertion-order queries use `stamp`, while the
//! tid-then-idx order used by the tiebreaker uses `EventId`'s `Ord` directly.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Arc;

use crate::event::{EventId, Label, Model, Tid, Val, Window};

/// Membership-only interface for internal graph cuts. Tree callers retain their
/// existing API; small causal prefixes need no tree allocation.
pub(crate) trait EventMembership {
    fn contains(&self, event: &EventId) -> bool;
}

impl EventMembership for BTreeSet<EventId> {
    fn contains(&self, event: &EventId) -> bool {
        BTreeSet::contains(self, event)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SmallEventSet {
    rows: [u64; 4],
}

impl SmallEventSet {
    /// None means the event cannot be represented; false means already present.
    fn insert(&mut self, event: EventId) -> Option<bool> {
        if event.idx >= 64 {
            return None;
        }
        let row = self.rows.get_mut(event.tid)?;
        let bit = 1u64 << event.idx;
        let fresh = *row & bit == 0;
        *row |= bit;
        Some(fresh)
    }

    fn pop_first(&mut self) -> Option<EventId> {
        for (tid, row) in self.rows.iter_mut().enumerate() {
            if *row != 0 {
                let idx = row.trailing_zeros() as usize;
                *row &= *row - 1;
                return Some(EventId::new(tid, idx));
            }
        }
        None
    }
}

impl EventMembership for SmallEventSet {
    #[inline]
    fn contains(&self, event: &EventId) -> bool {
        event.idx < 64
            && self
                .rows
                .get(event.tid)
                .is_some_and(|row| *row & (1u64 << event.idx) != 0)
    }
}

/// Exact strict causal prefix, compact in the common bounded graph domain.
#[derive(Debug)]
pub(crate) enum CausalPrefix {
    Small(SmallEventSet),
    Large(BTreeSet<EventId>),
}

impl EventMembership for CausalPrefix {
    #[inline]
    fn contains(&self, event: &EventId) -> bool {
        match self {
            Self::Small(set) => set.contains(event),
            Self::Large(set) => set.contains(event),
        }
    }
}

impl CausalPrefix {
    fn into_tree(self) -> BTreeSet<EventId> {
        match self {
            Self::Large(set) => set,
            Self::Small(mut set) => {
                let mut tree = BTreeSet::new();
                while let Some(event) = set.pop_first() {
                    tree.insert(event);
                }
                tree
            }
        }
    }
}

/// A set of the events of one graph, as a per-thread grid of generation tags: a cell is in
/// the set when its tag equals the current generation. Clearing is a generation bump, so a
/// query that needs a fresh set does no allocation once the grid has grown to size - which
/// is what lets the hot predicates ([`ExecutionGraph::unread_sends`],
/// [`ExecutionGraph::porf_reaches`], `consistent_mbox`) run without touching the allocator.
///
/// Marks are keyed by `(tid, idx)`, so one instance is only ever valid for the graph it was
/// [`begin`](Marks::begin)'d on.
#[derive(Default)]
pub(crate) struct Marks {
    cells: Vec<Vec<u64>>,
    gen: u64,
}

impl Marks {
    /// Clear the set and size it for `g` (O(threads), no allocation once grown).
    pub(crate) fn begin(&mut self, g: &ExecutionGraph) {
        self.gen += 1;
        self.grow(g);
    }

    /// Size the grid for a forward-grown graph without clearing existing marks.
    /// Committed RF-source marks survive append/pop DFS; newly appended source
    /// cells must exist before `insert`, whose out-of-grid behavior is deliberate.
    pub(crate) fn grow(&mut self, g: &ExecutionGraph) {
        if self.cells.len() < g.threads.len() {
            self.cells.resize_with(g.threads.len(), Vec::new);
        }
        for (row, thread) in self.cells.iter_mut().zip(g.threads.iter()) {
            if row.len() < thread.len() {
                row.resize(thread.len(), 0);
            }
        }
    }

    /// Add `e`; returns whether it was newly added (like `BTreeSet::insert`).
    ///
    /// An id outside the graph is accepted and simply not stored: callers mark rf sources,
    /// and a dangling source (one a cut removed) has to behave as it did when these sets
    /// were `BTreeSet`s — held, but matching no event of the graph.
    pub(crate) fn insert(&mut self, e: EventId) -> bool {
        match self.cells.get_mut(e.tid).and_then(|row| row.get_mut(e.idx)) {
            Some(cell) => {
                let fresh = *cell != self.gen;
                *cell = self.gen;
                fresh
            }
            None => true,
        }
    }

    /// Remove a mark only in the current generation; returns whether it existed.
    pub(crate) fn remove(&mut self, e: EventId) -> bool {
        match self.cells.get_mut(e.tid).and_then(|row| row.get_mut(e.idx)) {
            Some(cell) if *cell == self.gen => {
                *cell = 0;
                true
            }
            _ => false,
        }
    }

    pub(crate) fn contains(&self, e: EventId) -> bool {
        self.cells
            .get(e.tid)
            .and_then(|row| row.get(e.idx))
            .is_some_and(|&c| c == self.gen)
    }
}

/// Which events an [`EventIter`] yields.
#[derive(Clone, Copy, PartialEq)]
enum Kind {
    All,
    Send,
    Recv,
}

/// Walks a graph's events in `(tid, idx)` order, optionally keeping only sends or only
/// receives. Hand-rolled rather than `flat_map(..).filter(..)`: these three iterators drive
/// every consistency check, and the adapter stack was showing up as a top-of-stack cost of
/// its own.
pub struct EventIter<'a> {
    g: &'a ExecutionGraph,
    kind: Kind,
    tid: usize,
    idx: usize,
}

impl Iterator for EventIter<'_> {
    type Item = EventId;

    #[inline]
    fn next(&mut self) -> Option<EventId> {
        loop {
            let thread = self.g.threads.get(self.tid)?;
            if self.idx >= thread.len() {
                self.tid += 1;
                self.idx = 0;
                continue;
            }
            if self.kind != Kind::All && self.idx < 64 {
                let bits = match self.kind {
                    Kind::Send => thread.send_bits,
                    Kind::Recv => thread.recv_bits,
                    Kind::All => unreachable!(),
                } & (u64::MAX << self.idx);
                if bits != 0 {
                    let idx = bits.trailing_zeros() as usize;
                    self.idx = idx + 1;
                    return Some(EventId::new(self.tid, idx));
                }
                if thread.len() <= 64 {
                    self.tid += 1;
                    self.idx = 0;
                } else {
                    self.idx = 64;
                }
                continue;
            }
            let e = EventId::new(self.tid, self.idx);
            self.idx += 1;
            let wanted = match self.kind {
                Kind::All => true,
                Kind::Send => thread.labels[e.idx].is_send(),
                Kind::Recv => thread.labels[e.idx].is_recv(),
            };
            if wanted {
                return Some(e);
            }
        }
    }
}

thread_local! {
    /// Free list of [`Marks`] grids, so a caller that needs one across a recursive call
    /// (where a `thread_local` slot would be clobbered) still allocates nothing.
    static MARK_POOL: RefCell<Vec<Marks>> = const { RefCell::new(Vec::new()) };
}

/// A [`Marks`] borrowed from the per-thread pool and returned on drop.
pub(crate) struct PooledMarks(Option<Marks>);

impl PooledMarks {
    pub(crate) fn take() -> Self {
        PooledMarks(Some(
            MARK_POOL.with(|p| p.borrow_mut().pop()).unwrap_or_default(),
        ))
    }
}

impl std::ops::Deref for PooledMarks {
    type Target = Marks;
    fn deref(&self) -> &Marks {
        self.0.as_ref().expect("marks live until drop")
    }
}

impl std::ops::DerefMut for PooledMarks {
    fn deref_mut(&mut self) -> &mut Marks {
        self.0.as_mut().expect("marks live until drop")
    }
}

impl Drop for PooledMarks {
    fn drop(&mut self) {
        if let Some(m) = self.0.take() {
            MARK_POOL.with(|p| p.borrow_mut().push(m));
        }
    }
}

/// Per-thread scratch for the graph queries. Workers never share it (one instance per
/// thread), and no query here is re-entrant, so each borrows for the length of one call.
#[derive(Default)]
struct GraphScratch {
    /// Marked sends: read sources ([`ExecutionGraph::unread_sends`]).
    read: Marks,
    /// Visited set of a porf traversal ([`ExecutionGraph::porf_reaches`]).
    seen: Marks,
    /// Traversal stack, reused across porf walks.
    stack: Vec<EventId>,
    /// DFS colours for [`ExecutionGraph::is_porf_acyclic`] (0 unseen / 1 on stack / 2 done).
    color: Vec<Vec<u8>>,
    /// DFS stack for [`ExecutionGraph::is_porf_acyclic`]: (event, next predecessor slot).
    acyclic_stack: Vec<(EventId, u8)>,
    /// New stamp per old stamp for a [`restrict`](ExecutionGraph::restrict) (`u64::MAX`
    /// while a stamp is still marked as removed).
    rank: Vec<u64>,
}

thread_local! {
    static GSCRATCH: RefCell<GraphScratch> = RefCell::new(GraphScratch::default());
}

/// Event record retained for source compatibility. Graph storage separates its
/// immutable label from its mutable annotations to avoid cloning labels on cuts.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct StoredEvent {
    pub label: Label,
    pub stamp: u64,
    /// `rf(r)` for a receive `r`: `Some(send)` reads that send, `None` reads nothing (⊥) or
    /// is unassigned — the two are deliberately not distinguished, matching
    /// [`reads_from`](ExecutionGraph::reads_from). `None` for every non-receive event and
    /// never read for them.
    rf: Option<EventId>,
    /// The value a nondet event resolved to (Algorithm 1, line 6): `Some` once assigned,
    /// `None` before assignment and for every non-nondet event.
    nd: Option<Val>,
}

/// Mutable annotations are separate from immutable event labels. Cuts and RF
/// changes copy only annotations; their label prefixes share one allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PackedRf(u64);

impl PackedRf {
    const NONE: Self = Self(u64::MAX);
    const WIDE: Self = Self(u64::MAX - 1);

    fn encode(source: Option<EventId>) -> Self {
        let Some(source) = source else {
            return Self::NONE;
        };
        let (Ok(tid), Ok(idx)) = (u32::try_from(source.tid), u32::try_from(source.idx)) else {
            return Self::WIDE;
        };
        let packed = (u64::from(tid) << 32) | u64::from(idx);
        if packed >= Self::WIDE.0 {
            Self::WIDE
        } else {
            Self(packed)
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct EventMeta {
    stamp: u64,
    rf: PackedRf,
    nd: Option<Val>,
    /// Exact program prefix after this event, scoped by graph namespace.
    program_prefix: u64,
}

#[cfg(test)]
mod program_prefix_tests {
    use super::*;
    use crate::event::Pred;

    #[test]
    fn handles_follow_exact_prefixes_through_mutation_cut_clone_and_namespace_reset() {
        let mut graph = ExecutionGraph::new();
        let a = graph.add_event(0, Label::send(Model::Asyn, 1, "a"));
        let b = graph.add_event(0, Label::send(Model::Asyn, 1, "b"));
        let receive = graph.add_event(1, Label::recv_nb(Pred::any()));
        graph.set_rf(receive, Some(b));
        let choice = graph.add_event(1, Label::nondet(["x", "y"]));
        graph.set_nd(choice, "x".into());
        let send = graph.add_event(1, Label::send(Model::Asyn, 0, "tail"));
        let key = graph.canonical_key();
        assert_eq!(graph.program_prefix(1), None);
        graph.reset_program_prefix_namespace(17);
        for (event, token) in [(a, 10), (b, 11), (receive, 20), (choice, 21), (send, 22)] {
            graph.set_program_prefix(event, token);
        }
        assert_eq!(graph.program_prefix(2), Some(0));
        assert_eq!(graph.canonical_key(), key);
        let snapshot = graph.clone();

        let cut = graph.restrict_to_lens(&[1, 3]);
        assert_eq!(cut.program_prefix_namespace(), 17);
        assert_eq!(cut.program_prefix(0), Some(10));
        assert_eq!(cut.reads_from(receive), None);
        assert_eq!(cut.program_prefix(1), None);
        assert_eq!(snapshot.program_prefix(1), Some(22));

        graph.set_rf(receive, Some(b));
        assert_eq!(graph.program_prefix(1), Some(22));
        graph.set_rf(receive, Some(a));
        assert_eq!(graph.program_prefix(1), None);
        assert_eq!(graph.program_prefix(0), Some(11));
        for (event, token) in [(receive, 30), (choice, 31), (send, 32)] {
            graph.set_program_prefix(event, token);
        }
        graph.set_nd(choice, "x".into());
        assert_eq!(graph.program_prefix(1), Some(32));
        graph.set_nd(choice, "y".into());
        assert_eq!(graph.stored(receive).program_prefix, 30);
        assert_eq!(graph.program_prefix(1), None);
        graph.set_program_prefix(send, 42);

        let checkpoint = graph.checkpoint();
        let fresh = graph.add_event(1, Label::recv(Pred::any()));
        graph.set_rf_forward(fresh, Some(a));
        graph.set_program_prefix(fresh, 50);
        graph.set_rf_forward(fresh, Some(b));
        assert_eq!(graph.program_prefix(1), None);
        graph.restore_append(checkpoint, fresh);
        assert_eq!(graph.program_prefix(1), Some(42));
        graph.reset_program_prefix_namespace(18);
        assert_eq!(graph.program_prefix(0), None);
        assert_eq!(graph.program_prefix(1), None);
        assert_eq!(snapshot.program_prefix(1), Some(22));
    }
}

struct ThreadEvents {
    labels: Arc<Vec<Label>>,
    metadata: Vec<EventMeta>,
    /// Only out-of-range RF coordinates and the two reserved encodings need
    /// this source map. It is shared by snapshots and copied only on mutation.
    wide_rf: Option<Arc<BTreeMap<usize, EventId>>>,
    /// Kind indexes for the first 64 logical positions. Longer suffixes keep
    /// the ordinary label scan, so graph size is unrestricted.
    send_bits: u64,
    recv_bits: u64,
}

const fn prefix_bits(len: usize) -> u64 {
    if len >= 64 {
        u64::MAX
    } else {
        (1u64 << len) - 1
    }
}

impl std::fmt::Debug for ThreadEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ThreadEvents")
            .field("labels", &&self.labels[..self.metadata.len()])
            .field("metadata", &DebugMetadata(self))
            .finish()
    }
}

struct DebugMetadata<'a>(&'a ThreadEvents);

impl std::fmt::Debug for DebugMetadata<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct Entry<'a>(&'a ThreadEvents, usize);
        impl std::fmt::Debug for Entry<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let meta = &self.0.metadata[self.1];
                f.debug_struct("EventMeta")
                    .field("stamp", &meta.stamp)
                    .field("rf", &self.0.rf_at(self.1))
                    .field("nd", &meta.nd)
                    .field("program_prefix", &meta.program_prefix)
                    .finish()
            }
        }
        f.debug_list()
            .entries((0..self.0.len()).map(|idx| Entry(self.0, idx)))
            .finish()
    }
}

thread_local! {
    static EVENT_POOL: RefCell<Vec<Vec<EventMeta>>> = const { RefCell::new(Vec::new()) };
}

impl ThreadEvents {
    fn take_metadata(capacity: usize) -> Vec<EventMeta> {
        if capacity == 0 {
            return Vec::new();
        }
        let mut events = EVENT_POOL.with(|pool| {
            let mut pool = pool.borrow_mut();
            let slot = pool.iter().position(|v| v.capacity() >= capacity);
            slot.map(|i| pool.swap_remove(i))
                .or_else(|| pool.pop())
                .unwrap_or_default()
        });
        events.reserve(capacity);
        events
    }

    fn with_capacity(capacity: usize) -> Self {
        Self {
            labels: Arc::new(Vec::new()),
            metadata: Self::take_metadata(capacity),
            wide_rf: None,
            send_bits: 0,
            recv_bits: 0,
        }
    }

    fn push_event(&mut self, label: Label, meta: EventMeta) {
        let prefix_len = self.metadata.len();
        if prefix_len < 64 {
            let bit = 1u64 << prefix_len;
            if label.is_send() {
                self.send_bits |= bit;
            }
            if label.is_recv() {
                self.recv_bits |= bit;
            }
        }
        if Arc::get_mut(&mut self.labels).is_none() {
            // A restricted row can retain backing labels beyond its logical end.
            // Copy only its surviving prefix when an append finally needs ownership.
            let mut labels = Vec::with_capacity(prefix_len.saturating_add(1));
            labels.extend(self.labels[..prefix_len].iter().cloned());
            self.labels = Arc::new(labels);
        }
        let labels = Arc::get_mut(&mut self.labels).expect("label row is uniquely owned");
        labels.truncate(prefix_len);
        labels.push(label);
        self.metadata.push(meta);
    }

    fn truncate_events(&mut self, len: usize) {
        self.metadata.truncate(len);
        if let Some(wide) = &mut self.wide_rf {
            if wide.range(len..).next().is_some() {
                Arc::make_mut(wide).retain(|&idx, _| idx < len);
                if wide.is_empty() {
                    self.wide_rf = None;
                }
            }
        }
        self.send_bits &= prefix_bits(len);
        self.recv_bits &= prefix_bits(len);
        // A retained snapshot may still need the suffix; otherwise drop it now.
        if let Some(labels) = Arc::get_mut(&mut self.labels) {
            labels.truncate(len);
        }
    }

    #[inline]
    fn decode_rf(&self, idx: usize, rf: PackedRf) -> Option<EventId> {
        if rf == PackedRf::NONE {
            None
        } else if rf == PackedRf::WIDE {
            Some(
                *self
                    .wide_rf
                    .as_ref()
                    .and_then(|wide| wide.get(&idx))
                    .expect("wide RF metadata must have a source entry"),
            )
        } else {
            Some(EventId::new((rf.0 >> 32) as usize, (rf.0 as u32) as usize))
        }
    }

    #[inline]
    fn rf_at(&self, idx: usize) -> Option<EventId> {
        self.decode_rf(idx, self.metadata[idx].rf)
    }

    fn set_rf_at(&mut self, idx: usize, source: Option<EventId>) {
        let packed = PackedRf::encode(source);
        if packed == PackedRf::WIDE {
            let wide = self
                .wide_rf
                .get_or_insert_with(|| Arc::new(BTreeMap::new()));
            Arc::make_mut(wide).insert(idx, source.expect("wide RF represents a source"));
        } else if self.metadata[idx].rf == PackedRf::WIDE {
            let wide = self.wide_rf.as_mut().expect("wide RF source map exists");
            Arc::make_mut(wide).remove(&idx);
            if wide.is_empty() {
                self.wide_rf = None;
            }
        }
        self.metadata[idx].rf = packed;
    }
}

impl Clone for ThreadEvents {
    fn clone(&self) -> Self {
        let mut metadata = Self::take_metadata(self.len().saturating_add(1));
        metadata.extend_from_slice(&self.metadata);
        Self {
            labels: Arc::clone(&self.labels),
            metadata,
            wide_rf: self.wide_rf.clone(),
            send_bits: self.send_bits,
            recv_bits: self.recv_bits,
        }
    }
}

impl std::ops::Deref for ThreadEvents {
    type Target = Vec<EventMeta>;
    fn deref(&self) -> &Self::Target {
        &self.metadata
    }
}

impl std::ops::DerefMut for ThreadEvents {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.metadata
    }
}

impl Drop for ThreadEvents {
    fn drop(&mut self) {
        if self.metadata.capacity() == 0 || self.metadata.capacity() > 1024 {
            return;
        }
        self.metadata.clear();
        let _ = EVENT_POOL.try_with(|pool| {
            let mut pool = pool.borrow_mut();
            if pool.len() < 32 {
                pool.push(std::mem::take(&mut self.metadata));
            }
        });
    }
}

/// Metadata needed to undo one forward append. This is a value, rather than a
/// graph clone or a vector of prefix lengths: nested forward DFS can save it on
/// the stack and restore checkpoints in reverse order without allocating.
#[derive(Clone, Copy)]
pub(crate) struct AppendCheckpoint {
    threads: usize,
    next_stamp: u64,
    backward_rf: usize,
    send_count: usize,
    model_mask: u8,
    porf_acyclic: u8,
}

/// Stamp invariant: within each thread, stamps strictly increase with `idx`.
/// `add_event` appends with a growing counter, and `restrict` keeps po-prefixes while
/// preserving relative stamp order. Hence any stamp-downward-closed event set is
/// automatically po-prefix-closed per thread, which is what makes `restrict`'s keep
/// sets valid.
#[derive(Debug, Default)]
pub struct ExecutionGraph {
    /// Optimization-only arena identity; absent from graph keys and ordering.
    program_prefix_namespace: u64,
    /// `threads[t]` holds the events of thread `t` in program order; the vector
    /// index is the event's `idx`, so `po` is exactly the vector order. Each event carries
    /// its own `rf`/`nd` inline in the metadata row. No inverse (read-by) map is cached:
    /// `is_read`/`unread_sends` scan the events, which stays correct even through the
    /// transient double-read states that arise during exploration.
    ///
    /// Each graph owns its mutable annotations. Cloning copies their thin rows
    /// from a bounded allocation pool; RF/ND mutations update them directly.
    /// Immutable label backing remains shared until an append needs its own prefix.
    threads: Vec<ThreadEvents>,
    /// Monotonic insertion counter; the next added event gets this stamp.
    next_stamp: u64,
    /// 0 unknown / 1 acyclic / 2 cyclic. Queries may cache this on a shared graph;
    /// relaxed ordering suffices because every mutation requires exclusive access.
    porf_acyclic: AtomicU8,
    /// RF edges that do not point forward in insertion order. Zero proves that
    /// stamps are a topological ordering of po ∪ rf.
    backward_rf: usize,
    /// Sends surviving in the graph; maintained by append and prefix restriction.
    send_count: usize,
    /// One bit per communication model present among the surviving sends.
    model_mask: u8,
}

impl Clone for ExecutionGraph {
    fn clone(&self) -> Self {
        Self {
            threads: self.threads.clone(),
            program_prefix_namespace: self.program_prefix_namespace,
            next_stamp: self.next_stamp,
            backward_rf: self.backward_rf,
            send_count: self.send_count,
            model_mask: self.model_mask,
            porf_acyclic: AtomicU8::new(self.porf_acyclic.load(Ordering::Relaxed)),
        }
    }
}

impl ExecutionGraph {
    pub(crate) fn program_prefix_namespace(&self) -> u64 {
        self.program_prefix_namespace
    }

    pub(crate) fn reset_program_prefix_namespace(&mut self, namespace: u64) {
        debug_assert_ne!(namespace, 0);
        if self.program_prefix_namespace == namespace {
            return;
        }
        for row in &mut self.threads {
            for event in &mut row.metadata {
                event.program_prefix = 0;
            }
        }
        self.program_prefix_namespace = namespace;
    }

    pub(crate) fn program_prefix(&self, tid: Tid) -> Option<u64> {
        if self.program_prefix_namespace == 0 {
            return None;
        }
        match self.threads.get(tid).and_then(|row| row.last()) {
            None => Some(0), // The reserved empty-trace token.
            Some(event) => (event.program_prefix != 0).then_some(event.program_prefix),
        }
    }

    pub(crate) fn set_program_prefix(&mut self, event: EventId, token: u64) {
        debug_assert_ne!(self.program_prefix_namespace, 0);
        self.stored_mut(event).program_prefix = token;
    }

    fn invalidate_program_prefixes(&mut self, event: EventId) {
        if self.program_prefix_namespace != 0 {
            for meta in &mut self.threads[event.tid].metadata[event.idx..] {
                meta.program_prefix = 0;
            }
        }
    }
    pub fn new() -> Self {
        Self {
            porf_acyclic: AtomicU8::new(1),
            ..Self::default()
        }
    }

    pub fn num_threads(&self) -> usize {
        self.threads.len()
    }

    /// Number of sends in O(1), without scanning labels. In particular, checking an
    /// exploration's send bound does not rescan the whole graph on every append.
    pub fn num_sends(&self) -> usize {
        self.send_count
    }

    /// Whether the surviving graph contains a send using `model`.
    pub(crate) fn uses_model(&self, model: Model) -> bool {
        self.model_mask & (1 << model as u8) != 0
    }

    /// Save an allocation-free checkpoint immediately before adding one event.
    /// Existing events must not be modified between checkpoint and restore;
    /// changing the appended receive's rf or nondet value is permitted. Nested
    /// append/restore pairs must be restored in reverse order.
    pub(crate) fn checkpoint(&self) -> AppendCheckpoint {
        AppendCheckpoint {
            threads: self.threads.len(),
            next_stamp: self.next_stamp,
            backward_rf: self.backward_rf,
            send_count: self.send_count,
            model_mask: self.model_mask,
            porf_acyclic: self.porf_acyclic.load(Ordering::Relaxed),
        }
    }

    /// Undo the single suffix event added after `checkpoint`. Prefix rows keep
    /// their allocation. If an observer or donated work item retained a graph
    /// clone, its independently owned annotations protect that snapshot. Label
    /// copy-on-write protects any shared suffix.
    pub(crate) fn restore_append(&mut self, checkpoint: AppendCheckpoint, event: EventId) {
        debug_assert_eq!(self.next_stamp, checkpoint.next_stamp + 1);
        debug_assert_eq!(self.threads.len(), checkpoint.threads.max(event.tid + 1));
        debug_assert_eq!(self.thread_len(event.tid), event.idx + 1);
        debug_assert_eq!(self.stamp(event), checkpoint.next_stamp);
        if event.tid < checkpoint.threads {
            self.threads[event.tid].truncate_events(event.idx);
        } else {
            debug_assert_eq!(event.idx, 0);
        }
        self.threads.truncate(checkpoint.threads);
        self.next_stamp = checkpoint.next_stamp;
        self.backward_rf = checkpoint.backward_rf;
        self.send_count = checkpoint.send_count;
        self.model_mask = checkpoint.model_mask;
        self.porf_acyclic
            .store(checkpoint.porf_acyclic, Ordering::Relaxed);
    }

    pub fn thread_len(&self, tid: Tid) -> usize {
        self.threads.get(tid).map_or(0, |t| t.len())
    }

    /// Whether `e` denotes an event present in the graph.
    pub fn contains(&self, e: EventId) -> bool {
        e.idx < self.thread_len(e.tid)
    }

    fn stored(&self, e: EventId) -> &EventMeta {
        &self.threads[e.tid][e.idx]
    }

    fn stored_mut(&mut self, e: EventId) -> &mut EventMeta {
        // Annotation rows are graph-owned; labels remain independently shared.
        &mut self.threads[e.tid][e.idx]
    }

    pub fn label(&self, e: EventId) -> &Label {
        let thread = &self.threads[e.tid];
        assert!(e.idx < thread.len(), "event must belong to the graph");
        &thread.labels[e.idx]
    }

    pub fn stamp(&self, e: EventId) -> u64 {
        self.stored(e).stamp
    }

    /// Add `label` as the latest event (in insertion order) of thread `tid`; returns its id.
    pub fn add_event(&mut self, tid: Tid, label: Label) -> EventId {
        if tid >= self.threads.len() {
            self.threads
                .resize_with(tid + 1, || ThreadEvents::with_capacity(0));
        }
        self.send_count += usize::from(label.is_send());
        if let Some(model) = label.model() {
            self.model_mask |= 1 << model as u8;
        }
        let idx = self.threads[tid].len();
        let stamp = self.next_stamp;
        self.next_stamp += 1;
        self.threads[tid].push_event(
            label,
            EventMeta {
                stamp,
                rf: PackedRf::NONE,
                nd: None,
                program_prefix: 0,
            },
        );
        EventId::new(tid, idx)
    }

    /// Point receive `recv` at source `src` (`None` means it reads nothing), dropping any
    /// previous edge.
    pub fn set_rf(&mut self, recv: EventId, src: Option<EventId>) {
        debug_assert!(
            self.contains(recv) && self.label(recv).is_recv(),
            "set_rf target must be an existing receive"
        );
        let old = self.threads[recv.tid].rf_at(recv.idx);
        if old == src {
            return;
        }
        let backwards =
            |source: EventId| !self.contains(source) || self.stamp(source) >= self.stamp(recv);
        let removed_backwards = usize::from(old.is_some_and(backwards));
        let added_backwards = usize::from(src.is_some_and(backwards));
        self.backward_rf = self.backward_rf - removed_backwards + added_backwards;
        // Removing an edge preserves acyclicity; adding any edge may close a
        // cycle if other rf edges run backwards, so invalidate conservatively.
        if src.is_some() || self.porf_acyclic.load(Ordering::Relaxed) != 1 {
            self.porf_acyclic.store(0, Ordering::Relaxed);
        }
        let same_value = self.same_receive_value(old, src);
        self.threads[recv.tid].set_rf_at(recv.idx, src);
        if !same_value {
            self.invalidate_program_prefixes(recv);
        }
    }

    /// Set the rf of the freshly appended, insertion-maximal receive to an
    /// existing older send. Its only incident causal edges are incoming, so this
    /// cannot change acyclicity or the count of backward-stamp rf edges. This is
    /// the forward DFS counterpart of the general [`Self::set_rf`] operation.
    pub(crate) fn set_rf_forward(&mut self, receive: EventId, source: Option<EventId>) {
        debug_assert!(self.label(receive).is_recv());
        debug_assert_eq!(self.stamp(receive) + 1, self.next_stamp);
        debug_assert!(source.is_none_or(|send| {
            self.contains(send)
                && self.label(send).is_send()
                && self.stamp(send) < self.stamp(receive)
        }));
        let old = self.threads[receive.tid].rf_at(receive.idx);
        debug_assert!(old.is_none_or(|send| {
            self.contains(send)
                && self.label(send).is_send()
                && self.stamp(send) < self.stamp(receive)
        }));
        if old != source {
            let same_value = self.same_receive_value(old, source);
            self.threads[receive.tid].set_rf_at(receive.idx, source);
            if !same_value {
                self.invalidate_program_prefixes(receive);
            }
        }
    }

    /// Program prefixes depend on delivered values, while graph consistency and
    /// source ordering continue to depend on full source identities. Only two
    /// contained sends with equal payloads preserve the local continuation.
    fn same_receive_value(&self, old: Option<EventId>, new: Option<EventId>) -> bool {
        match (old, new) {
            (Some(old), Some(new)) if self.contains(old) && self.contains(new) => {
                matches!((self.label(old), self.label(new)),
                    (Label::Send { val: left, .. }, Label::Send { val: right, .. }) if left == right)
            }
            _ => false,
        }
    }

    /// Source read by `r`: `Some(send)`, or `None` for nothing read.
    ///
    /// "No rf assigned yet" and an explicit "reads nothing" are not distinguished; both
    /// are `None`. The explorer calls `set_rf` immediately after adding a receive, so no
    /// receive ever reaches a consistency check with an unassigned rf.
    pub fn reads_from(&self, r: EventId) -> Option<EventId> {
        if self.contains(r) {
            self.threads[r.tid].rf_at(r.idx)
        } else {
            None
        }
    }

    /// Mark assigned rf sources directly in the stored rows, avoiding an event
    /// iterator and a second graph lookup per receive. Non-receives have no rf.
    pub(crate) fn mark_read_sources(&self, skip: Option<EventId>, read: &mut Marks) {
        read.begin(self);
        for (tid, thread) in self.threads.iter().enumerate() {
            for (idx, event) in thread.iter().enumerate() {
                if skip == Some(EventId::new(tid, idx)) {
                    continue;
                }
                if let Some(source) = thread.decode_rf(idx, event.rf) {
                    read.insert(source);
                }
            }
        }
    }

    /// A prefix restriction normalizes removed RF sources to bottom. Given a
    /// consistent original graph, only blocking receives that lost their source
    /// can become ill-formed; `skip` is the receive reassigned by a revisit.
    pub(crate) fn retained_receive_sources_valid(&self, skip: EventId) -> bool {
        self.threads.iter().enumerate().all(|(tid, thread)| {
            thread.iter().enumerate().all(|(idx, event)| {
                EventId::new(tid, idx) == skip
                    || event.rf != PackedRf::NONE
                    || thread.labels[idx].blocking() != Some(true)
            })
        })
    }

    /// Validate retained blocking RF sources without materializing a revisit cut.
    pub(crate) fn blocking_sources_survive_revisit(
        &self,
        receive: EventId,
        send: EventId,
        send_prefix: &impl EventMembership,
    ) -> bool {
        let receive_stamp = self.stamp(receive);
        let kept = |event: EventId| {
            self.stamp(event) <= receive_stamp || send_prefix.contains(&event) || event == send
        };
        self.threads.iter().enumerate().all(|(tid, thread)| {
            thread.iter().enumerate().all(|(idx, event)| {
                let id = EventId::new(tid, idx);
                id == receive
                    || thread.labels[idx].blocking() != Some(true)
                    || !kept(id)
                    || thread.decode_rf(idx, event.rf).is_some_and(kept)
            })
        })
    }

    /// Whether `r` reads nothing (explicit, or no source assigned).
    pub fn reads_bottom(&self, r: EventId) -> bool {
        self.reads_from(r).is_none()
    }

    /// Whether send `s` is read by some receive. Scans events (non-receives carry `rf =
    /// None`, so they never match); no inverse map is kept.
    pub fn is_read(&self, s: EventId) -> bool {
        self.iter_events()
            .any(|e| self.threads[e.tid].rf_at(e.idx) == Some(s))
    }

    /// Assign the chosen value `v` to nondet event `e` (Algorithm 1, line 6), replacing
    /// any previous choice.
    pub fn set_nd(&mut self, e: EventId, v: Val) {
        debug_assert!(
            self.contains(e) && self.label(e).is_nondet(),
            "set_nd target must be an existing nondet event"
        );
        if self.stored(e).nd != Some(v) {
            self.stored_mut(e).nd = Some(v);
            self.invalidate_program_prefixes(e);
        }
    }

    /// The value nondet event `e` resolved to (`None` if not yet assigned).
    pub fn nd_value(&self, e: EventId) -> Option<&Val> {
        if self.contains(e) {
            self.stored(e).nd.as_ref()
        } else {
            None
        }
    }

    /// All nondet events in `(tid, idx)` order.
    pub fn nondet_events(&self) -> Vec<EventId> {
        self.all_events()
            .into_iter()
            .filter(|&e| self.label(e).is_nondet())
            .collect()
    }

    pub fn send_model(&self, e: EventId) -> Option<Model> {
        self.label(e).model()
    }

    /// A send's delivery [`Window`] (`None` for a non-send or a missing event). The seam
    /// through which the time-intervals filter reads windows off the graph.
    pub fn send_window(&self, e: EventId) -> Option<Window> {
        if self.contains(e) {
            self.label(e).window()
        } else {
            None
        }
    }

    /// All events in `(tid, idx)` order, without allocating a `Vec`: the iterator
    /// counterpart of [`all_events`](Self::all_events).
    #[inline]
    pub fn iter_events(&self) -> EventIter<'_> {
        EventIter {
            g: self,
            kind: Kind::All,
            tid: 0,
            idx: 0,
        }
    }

    /// All events in `(tid, idx)` order.
    pub fn all_events(&self) -> Vec<EventId> {
        self.iter_events().collect()
    }

    /// Sends in `(tid, idx)` order, without allocating — the iterator counterpart of
    /// [`sends`](Self::sends) for the consistency predicates.
    #[inline]
    pub fn iter_sends(&self) -> EventIter<'_> {
        EventIter {
            g: self,
            kind: Kind::Send,
            tid: 0,
            idx: 0,
        }
    }

    /// Receives in `(tid, idx)` order, without allocating — the iterator counterpart of
    /// [`recvs`](Self::recvs).
    #[inline]
    pub fn iter_recvs(&self) -> EventIter<'_> {
        EventIter {
            g: self,
            kind: Kind::Recv,
            tid: 0,
            idx: 0,
        }
    }

    /// All events in insertion order.
    pub fn events_by_stamp(&self) -> Vec<EventId> {
        let mut v = self.all_events();
        v.sort_by_key(|&e| self.stamp(e));
        v
    }

    pub fn sends(&self) -> Vec<EventId> {
        self.iter_sends().collect()
    }

    pub fn recvs(&self) -> Vec<EventId> {
        self.iter_recvs().collect()
    }

    /// Unread sends `G.US`: sends no receive reads, in `(tid, idx)` order.
    ///
    /// The read sources are marked in a reusable per-thread grid rather than collected into
    /// a `BTreeSet`, so only the result vector is allocated.
    pub fn unread_sends(&self) -> Vec<EventId> {
        GSCRATCH.with(|s| {
            let read = &mut s.borrow_mut().read;
            read.begin(self);
            for e in self.iter_events() {
                if let Some(src) = self.threads[e.tid].rf_at(e.idx) {
                    read.insert(src);
                }
            }
            self.iter_events()
                .filter(|&e| self.label(e).is_send() && !read.contains(e))
                .collect()
        })
    }

    /// `matches(s, r)`: `mval` with destination, i.e. `dst(s) = tid(r)` and `val(s)` is
    /// in `vals(r)`.
    pub fn matches(&self, s: EventId, r: EventId) -> bool {
        let (Label::Send { dst, val, .. }, Label::Recv { pred, .. }) =
            (self.label(s), self.label(r))
        else {
            return false;
        };
        *dst == r.tid && pred.test_sym(*val)
    }

    /// Immediate predecessors of `e` under `po` and `rf`: its po-predecessor and, if `e`
    /// is a receive, the send it reads.
    fn porf_preds(&self, e: EventId) -> Vec<EventId> {
        let mut preds = Vec::new();
        if e.idx > 0 {
            preds.push(EventId::new(e.tid, e.idx - 1));
        }
        if let Some(s) = self.reads_from(e) {
            preds.push(s);
        }
        preds
    }

    /// All `e'` with `(e', e)` in `G.porf`. Here `porf` is the irreflexive transitive
    /// closure of `po` and `rf`, so the returned set never contains `e` unless `e` lies
    /// on a causal cycle. `porf_reaches` uses the same strict convention.
    pub fn porf_prefix(&self, e: EventId) -> BTreeSet<EventId> {
        self.causal_prefix(e).into_tree()
    }

    /// Allocation-free exact prefix in at most four 64-event thread rows.
    /// Predecessors are traversed directly, including backwards RF edges and
    /// cycles. No previously cached closure is intersected with a cut mask.
    pub(crate) fn causal_prefix(&self, e: EventId) -> CausalPrefix {
        fn enqueue(seen: &mut SmallEventSet, frontier: &mut SmallEventSet, event: EventId) -> bool {
            match seen.insert(event) {
                None => false,
                Some(false) => true,
                Some(true) => {
                    frontier
                        .insert(event)
                        .expect("seen event fits the same domain");
                    true
                }
            }
        }
        if self.threads.len() > 4 || self.threads.iter().any(|thread| thread.len() > 64) {
            return CausalPrefix::Large(self.porf_prefix_tree(e));
        }
        let mut seen = SmallEventSet::default();
        let mut frontier = SmallEventSet::default();
        if e.idx > 0 && !enqueue(&mut seen, &mut frontier, EventId::new(e.tid, e.idx - 1)) {
            return CausalPrefix::Large(self.porf_prefix_tree(e));
        }
        if self
            .reads_from(e)
            .is_some_and(|source| !enqueue(&mut seen, &mut frontier, source))
        {
            return CausalPrefix::Large(self.porf_prefix_tree(e));
        }
        while let Some(event) = frontier.pop_first() {
            if event.idx > 0
                && !enqueue(
                    &mut seen,
                    &mut frontier,
                    EventId::new(event.tid, event.idx - 1),
                )
            {
                return CausalPrefix::Large(self.porf_prefix_tree(e));
            }
            if self
                .reads_from(event)
                .is_some_and(|source| !enqueue(&mut seen, &mut frontier, source))
            {
                return CausalPrefix::Large(self.porf_prefix_tree(e));
            }
        }
        CausalPrefix::Small(seen)
    }

    fn porf_prefix_tree(&self, e: EventId) -> BTreeSet<EventId> {
        let mut seen = BTreeSet::new();
        let mut queue: VecDeque<EventId> = VecDeque::new();
        for p in self.porf_preds(e) {
            if seen.insert(p) {
                queue.push_back(p);
            }
        }
        while let Some(x) = queue.pop_front() {
            for p in self.porf_preds(x) {
                if seen.insert(p) {
                    queue.push_back(p);
                }
            }
        }
        seen
    }

    /// `porf_prefix(e)` marked into caller-owned buffers instead of returned as a set: the
    /// form the consistency predicates use when they need one prefix tested against many
    /// events. `seen` is cleared (and sized for this graph) first; `stack` is scratch.
    pub(crate) fn porf_prefix_into(&self, e: EventId, seen: &mut Marks, stack: &mut Vec<EventId>) {
        seen.begin(self);
        stack.clear();
        // Seeded with `e`'s predecessors, not `e`: the prefix is strict, so `e` is in it
        // only when it lies on a causal cycle (and is then reached as a predecessor).
        if e.idx > 0 {
            stack.push(EventId::new(e.tid, e.idx - 1));
        }
        if let Some(p) = self.reads_from(e) {
            stack.push(p);
        }
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if x.idx > 0 {
                stack.push(EventId::new(x.tid, x.idx - 1));
            }
            if let Some(p) = self.reads_from(x) {
                stack.push(p);
            }
        }
    }

    /// Whether `(a, b)` is in `G.porf` (strict).
    ///
    /// Same relation as `porf_prefix(b).contains(&a)`, but walks `b`'s predecessors with a
    /// reusable mark grid and stops at the first sighting of `a` instead of materialising
    /// the whole prefix - this is the form the consistency predicates call per pair.
    pub fn porf_reaches(&self, a: EventId, b: EventId) -> bool {
        GSCRATCH.with(|sc| {
            let GraphScratch { seen, stack, .. } = &mut *sc.borrow_mut();
            seen.begin(self);
            stack.clear();
            stack.push(b);
            while let Some(x) = stack.pop() {
                // The (at most two) porf predecessors of `x`, inlined to avoid the `Vec`
                // that `porf_preds` returns.
                if x.idx > 0 {
                    let p = EventId::new(x.tid, x.idx - 1);
                    if p == a {
                        return true;
                    }
                    if seen.insert(p) {
                        stack.push(p);
                    }
                }
                if let Some(p) = self.reads_from(x) {
                    if p == a {
                        return true;
                    }
                    if seen.insert(p) {
                        stack.push(p);
                    }
                }
            }
            false
        })
    }

    /// Strict porf reachability in a virtual po-prefix restriction, optionally
    /// erasing one receive's incoming RF edge before the query. Edges touching
    /// removed events are skipped, exactly as `restrict` normalizes their RF.
    /// The caller's `kept` predicate must not re-enter graph scratch queries.
    pub(crate) fn porf_reaches_kept(
        &self,
        from: EventId,
        to: EventId,
        kept: impl Fn(EventId) -> bool,
        skip_rf: Option<EventId>,
    ) -> bool {
        if !kept(from) || !kept(to) {
            return false;
        }
        GSCRATCH.with(|scratch| {
            let GraphScratch { seen, stack, .. } = &mut *scratch.borrow_mut();
            seen.begin(self);
            stack.clear();
            stack.push(to);
            while let Some(event) = stack.pop() {
                if event.idx > 0 {
                    let predecessor = EventId::new(event.tid, event.idx - 1);
                    if kept(predecessor) {
                        if predecessor == from {
                            return true;
                        }
                        if seen.insert(predecessor) {
                            stack.push(predecessor);
                        }
                    }
                }
                if Some(event) != skip_rf {
                    if let Some(predecessor) = self.reads_from(event) {
                        if kept(predecessor) {
                            if predecessor == from {
                                return true;
                            }
                            if seen.insert(predecessor) {
                                stack.push(predecessor);
                            }
                        }
                    }
                }
            }
            false
        })
    }

    /// Whether `po` and `rf` together are acyclic, i.e. no event reaches itself. This is
    /// a well-formedness requirement.
    ///
    /// An iterative three-colour DFS over `po` and `rf`, following the (at most two)
    /// predecessors of each event and reporting a cycle on a back edge to an ancestor
    /// still on the stack. Iterative rather than recursive so deep graphs cannot overflow
    /// the call stack.
    pub fn is_porf_acyclic(&self) -> bool {
        if self.backward_rf == 0 {
            return true;
        }
        match self.porf_acyclic.load(Ordering::Relaxed) {
            1 => return true,
            2 => return false,
            _ => {}
        }
        let result = GSCRATCH.with(|sc| {
            let GraphScratch {
                color,
                acyclic_stack: stack,
                ..
            } = &mut *sc.borrow_mut();
            self.porf_acyclic_with(color, stack)
        });
        self.porf_acyclic
            .store(if result { 1 } else { 2 }, Ordering::Relaxed);
        result
    }

    /// [`is_porf_acyclic`](Self::is_porf_acyclic) over caller-owned buffers, so the colour
    /// grid and the DFS stack are reused across calls instead of reallocated per check.
    fn porf_acyclic_with(&self, color: &mut Vec<Vec<u8>>, stack: &mut Vec<(EventId, u8)>) -> bool {
        // Colour per event: 0 = unseen, 1 = on the DFS stack, 2 = fully explored.
        color.resize_with(self.threads.len(), Vec::new);
        for (row, thread) in color.iter_mut().zip(self.threads.iter()) {
            row.clear();
            row.resize(thread.len(), 0);
        }
        stack.clear();

        for (tid, thread) in self.threads.iter().enumerate() {
            for idx in 0..thread.len() {
                if color[tid][idx] != 0 {
                    continue;
                }
                color[tid][idx] = 1;
                stack.push((EventId::new(tid, idx), 0));
                while let Some(&(e, slot)) = stack.last() {
                    // Slot 0 is the po-predecessor, slot 1 the rf source of a receive.
                    let mut s = slot;
                    let mut pred = None;
                    while s < 2 {
                        let cand = if s == 0 {
                            (e.idx > 0).then(|| EventId::new(e.tid, e.idx - 1))
                        } else {
                            self.reads_from(e)
                        };
                        s += 1;
                        if cand.is_some() {
                            pred = cand;
                            break;
                        }
                    }
                    stack.last_mut().unwrap().1 = s;
                    match pred {
                        Some(p) => match color[p.tid][p.idx] {
                            1 => return false, // back edge to an ancestor on the stack: cycle
                            0 => {
                                color[p.tid][p.idx] = 1;
                                stack.push((p, 0));
                            }
                            _ => {}
                        },
                        None => {
                            color[e.tid][e.idx] = 2;
                            stack.pop();
                        }
                    }
                }
            }
        }
        true
    }

    /// Restrict to `keep` (must be po-prefix-closed in every thread) and re-stamp the
    /// survivors, preserving their relative insertion order so it stays meaningful after
    /// the cut. This keeps the stamp invariant "stamp grows with idx within a thread". A
    /// surviving receive whose source was removed has its rf normalized to reading nothing,
    /// which well-formedness later rejects for a blocking receive.
    pub fn restrict(&self, keep: &BTreeSet<EventId>) -> ExecutionGraph {
        // Per thread, keep the maximal prefix fully contained in `keep`.
        let mut new_len = vec![0usize; self.threads.len()];
        for (tid, thread) in self.threads.iter().enumerate() {
            let mut k = 0;
            while k < thread.len() && keep.contains(&EventId::new(tid, k)) {
                k += 1;
            }
            new_len[tid] = k;
        }
        assert!(
            keep.iter()
                .all(|e| e.idx < new_len.get(e.tid).copied().unwrap_or(0)),
            "restrict expects a po-prefix-closed keep set"
        );
        self.restrict_to_lens(&new_len)
    }

    /// [`restrict`](Self::restrict) to a keep set given directly as per-thread prefix
    /// lengths: `keep_len[t]` events survive in thread `t`. Every keep set the explorer
    /// cuts with is po-prefix-closed, so it *is* a length vector; passing it in this form
    /// skips materialising the set (and, in the callers, building it at all).
    pub(crate) fn restrict_to_lens(&self, keep_len: &[usize]) -> ExecutionGraph {
        debug_assert!(
            keep_len.len() >= self.threads.len()
                || self.threads[keep_len.len()..].iter().all(|t| t.is_empty()),
            "keep_len must cover every non-empty thread"
        );
        let len_of = |tid: usize| {
            keep_len
                .get(tid)
                .copied()
                .unwrap_or(0)
                .min(self.thread_len(tid))
        };
        let kept = |e: EventId| e.idx < len_of(e.tid);

        // Nothing removed: the cut is the identity. Stamps are dense (`add_event` counts up
        // and every cut re-stamps densely), so the re-stamping would hand every event back
        // its own stamp — a thin-row clone is the same graph for less work. Whole classes of `Previous` cuts delete nothing at all.
        if (0..self.threads.len()).all(|tid| len_of(tid) == self.threads[tid].len()) {
            debug_assert_eq!(
                self.next_stamp as usize,
                self.threads.iter().map(|t| t.len()).sum::<usize>(),
                "identity restrict assumes dense stamps (as add_event and restrict produce)"
            );
            return self.clone();
        }

        GSCRATCH.with(|sc| {
            let GraphScratch { rank, .. } = &mut *sc.borrow_mut();

            // Re-stamp: survivors keep their relative insertion order, so the new stamp of an
            // event is the number of survivors ahead of it. Stamps are dense, so that is a
            // counting pass over the stamp axis - no sort (which used to be O(n log n) on
            // every cut, and every rf-choice reaches one).
            rank.clear();
            rank.resize(self.next_stamp as usize, u64::MAX);
            let mut backward_rf = 0;
            let mut send_count = 0;
            let mut model_mask = 0;
            for tid in 0..self.threads.len() {
                for idx in 0..len_of(tid) {
                    let event = &self.threads[tid][idx];
                    rank[event.stamp as usize] = 0; // marked as surviving
                    send_count += usize::from(self.threads[tid].labels[idx].is_send());
                    if let Some(model) = self.threads[tid].labels[idx].model() {
                        model_mask |= 1 << model as u8;
                    }
                    if self.backward_rf != 0
                        && self.threads[tid]
                            .decode_rf(idx, event.rf)
                            .is_some_and(|source| kept(source) && self.stamp(source) >= event.stamp)
                    {
                        backward_rf += 1;
                    }
                }
            }
            // `cut_from` = the oldest stamp that disappears: every survivor below it keeps
            // its own stamp, which is what lets an untouched thread be shared below.
            let mut cut_from = u64::MAX;
            let mut next = 0u64;
            for (old, slot) in rank.iter_mut().enumerate() {
                if *slot == u64::MAX {
                    cut_from = cut_from.min(old as u64);
                } else {
                    *slot = next;
                    next += 1;
                }
            }

            let mut threads: Vec<ThreadEvents> = Vec::with_capacity(self.threads.len());
            for tid in 0..self.threads.len() {
                let len = len_of(tid);
                // A thread that loses no event, whose events all predate the cut (so their
                // stamps are unchanged) and whose receives all still find their source, is
                // bit-for-bit the old thread: copy its thin annotation row and share
                // label backing without rebuilding individual event labels.
                let unchanged = len == self.threads[tid].len()
                    && self.threads[tid]
                        .last()
                        .is_none_or(|ev| ev.stamp < cut_from)
                    && self.threads[tid].iter().enumerate().all(|(idx, event)| {
                        self.threads[tid].decode_rf(idx, event.rf).is_none_or(kept)
                    });
                if unchanged {
                    threads.push(self.threads[tid].clone());
                    continue;
                }
                let mut thread = ThreadEvents {
                    labels: Arc::clone(&self.threads[tid].labels),
                    metadata: ThreadEvents::take_metadata(len.saturating_add(1)),
                    wide_rf: None,
                    send_bits: self.threads[tid].send_bits & prefix_bits(len),
                    recv_bits: self.threads[tid].recv_bits & prefix_bits(len),
                };
                let mut prefix_changed = false;
                for idx in 0..len {
                    let old = &self.threads[tid][idx];
                    // Carry `rf` forward, normalizing a source that did not survive to ⊥
                    // (well-formedness later rejects that for a blocking receive). idx is
                    // preserved by the cut, so a kept source keeps the same EventId. "Reading
                    // nothing" and "unassigned" are both `None`, exactly as `reads_from` treats
                    // them. `nd` is carried verbatim (idx-keyed choices stay valid).
                    let old_rf = self.threads[tid].decode_rf(idx, old.rf);
                    let rf = match old_rf {
                        Some(s) if kept(s) => Some(s),
                        _ => None,
                    };
                    prefix_changed |= rf != old_rf;
                    let packed_rf = PackedRf::encode(rf);
                    thread.metadata.push(EventMeta {
                        stamp: rank[old.stamp as usize],
                        rf: packed_rf,
                        nd: old.nd,
                        program_prefix: if prefix_changed {
                            0
                        } else {
                            old.program_prefix
                        },
                    });
                    if packed_rf == PackedRf::WIDE {
                        thread.set_rf_at(idx, rf);
                    }
                }
                threads.push(thread);
            }

            ExecutionGraph {
                threads,
                program_prefix_namespace: self.program_prefix_namespace,
                next_stamp: next,
                backward_rf,
                send_count,
                model_mask,
                porf_acyclic: AtomicU8::new(if self.porf_acyclic.load(Ordering::Relaxed) == 1 {
                    1
                } else {
                    0
                }),
            }
        })
    }

    /// Deterministic textual key of the graph's `(E, po, rf)` content, ignoring stamps.
    /// Two graphs with the same key are equal up to insertion order, so this backs the
    /// "no duplicate executions" guarantee.
    pub fn canonical_key(&self) -> String {
        let mut out = String::new();
        for (tid, thread) in self.threads.iter().enumerate() {
            // Skip empty thread slots: `restrict` can leave one behind (deleting a
            // thread's only event), and the resulting graph must compare equal to the
            // same graph reached without that slot.
            if thread.is_empty() {
                continue;
            }
            let _ = write!(out, "T{tid}:");
            for idx in 0..thread.len() {
                let _ = write!(out, " {}", label_key(&thread.labels[idx]));
            }
            out.push('\n');
        }
        out.push_str("rf:");
        for r in self.recvs() {
            match self.reads_from(r) {
                Some(s) => {
                    let _ = write!(out, " ⟨{},{}⟩<-⟨{},{}⟩", r.tid, r.idx, s.tid, s.idx);
                }
                None => {
                    let _ = write!(out, " ⟨{},{}⟩<-⊥", r.tid, r.idx);
                }
            }
        }
        // Two executions differing only in a nondet value must get different keys (they
        // are different graphs), so the chosen value is part of the key. Length-prefixed
        // and in (tid, idx) order, like the rest.
        out.push_str("\nnd:");
        for e in self.nondet_events() {
            match self.nd_value(e) {
                Some(v) => {
                    // Key by the resolved string, not the (nondeterministic) `Sym` id.
                    let vs = crate::intern::resolve(*v);
                    let _ = write!(out, " ⟨{},{}⟩={}:{vs}", e.tid, e.idx, vs.len());
                }
                None => {
                    let _ = write!(out, " ⟨{},{}⟩=?", e.tid, e.idx);
                }
            }
        }
        out
    }
}

// `ExecutionGraph` must stay `Send + Sync` so parallel exploration can hand subtrees to
// worker threads. Compile-time guard: this fails to build if any field ever reintroduces
// an `Rc` or other non-`Send`/`Sync` member.
const _: fn() = || {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<ExecutionGraph>();
};

// Free-form strings (val, pred repr, error msg) are length-prefixed so the key parses
// unambiguously left-to-right: a val containing "...) Sp2p(..." cannot collide with a
// pair of separate labels.
//
// `pub(crate)`: the viable-oracle memo (T2_ORACLE_SPEC §1.3) keys the revisiting label by this
// same canonical string (stable across `Sym` interning order, unlike `Debug`).
pub(crate) fn label_key(l: &Label) -> String {
    match l {
        Label::Send {
            model,
            dst,
            val,
            window,
        } => {
            let v = crate::intern::resolve(*val);
            // The window is part of graph identity, but the suffix is emitted ONLY for a
            // non-default (timed) window: an untimed send keeps the exact pre-window key,
            // so every existing key stays byte-identical. `@` after the length-prefixed
            // val (always after `)`) makes the suffix unambiguous to parse.
            let win = if window.is_untimed() {
                String::new()
            } else {
                format!("@{window}")
            };
            format!("S{model}({dst},{}:{v}){win}", v.len())
        }
        Label::Recv {
            pred,
            blocking,
            timing,
        } => {
            let b = if *blocking { "b" } else { "nb" };
            let suffix = if timing.is_timed() {
                format!("@{timing}")
            } else {
                String::new()
            };
            format!("R{b}[{}:{}]{suffix}", pred.repr().len(), pred.repr())
        }
        // The option set is program-fixed (identical across all executions), but
        // length-prefixed all the same so it never collides with a neighbouring label.
        Label::Nondet { set } => {
            let mut s = String::from("ND[");
            for v in set.iter() {
                let vs = crate::intern::resolve(*v);
                let _ = write!(s, "{}:{vs},", vs.len());
            }
            s.push(']');
            s
        }
        Label::Error { msg } => format!("E({}:{msg})", msg.len()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::Pred;

    #[test]
    fn add_event_assigns_positions_and_stamps() {
        let mut g = ExecutionGraph::new();
        let a = g.add_event(0, Label::send(Model::P2p, 1, "1"));
        let b = g.add_event(1, Label::recv(Pred::any()));
        let c = g.add_event(0, Label::send(Model::P2p, 1, "2"));
        assert_eq!(a, EventId::new(0, 0));
        assert_eq!(b, EventId::new(1, 0));
        assert_eq!(c, EventId::new(0, 1));
        assert_eq!(g.stamp(a), 0);
        assert_eq!(g.stamp(b), 1);
        assert_eq!(g.stamp(c), 2);
        assert_eq!(g.num_threads(), 2);
    }

    #[test]
    fn rf_and_unread() {
        let mut g = ExecutionGraph::new();
        let s = g.add_event(0, Label::send(Model::P2p, 1, "1"));
        let r = g.add_event(1, Label::recv(Pred::any()));
        assert_eq!(g.unread_sends(), vec![s]);
        g.set_rf(r, Some(s));
        assert_eq!(g.reads_from(r), Some(s));
        assert!(g.is_read(s));
        assert!(g.unread_sends().is_empty());
        // Re-pointing to nothing frees the send again.
        g.set_rf(r, None);
        assert!(g.reads_bottom(r));
        assert_eq!(g.unread_sends(), vec![s]);
    }

    #[test]
    fn nd_value_set_carried_through_restrict_and_key() {
        let mut g = ExecutionGraph::new();
        let n = g.add_event(0, Label::nondet(["0", "1"]));
        let s = g.add_event(0, Label::send(Model::P2p, 1, "x"));
        assert_eq!(g.nondet_events(), vec![n]);
        assert_eq!(g.nd_value(n), None); // not yet chosen

        g.set_nd(n, "1".into());
        assert_eq!(g.nd_value(n).map(|v| crate::intern::resolve(*v)), Some("1"));
        let key_one = g.canonical_key();

        // A different nondet value yields a different canonical key (different graph).
        let mut g2 = g.clone();
        g2.set_nd(n, "0".into());
        assert_ne!(key_one, g2.canonical_key());

        // restrict keeps the nondet choice of surviving events.
        let keep: BTreeSet<EventId> = [n].into_iter().collect();
        let h = g.restrict(&keep);
        assert!(!h.contains(s));
        assert_eq!(h.nd_value(n).map(|v| crate::intern::resolve(*v)), Some("1"));
    }

    #[test]
    fn untimed_send_label_key_is_byte_identical() {
        // An ordinary (ASAP) send must keep the exact pre-window key: no `@` suffix.
        let l = Label::send(Model::P2p, 2, "1");
        assert_eq!(label_key(&l), "Sp2p(2,1:1)");
        // send_within with ASAP is indistinguishable from send.
        let l2 = Label::send_within(Model::P2p, 2, "1", Window::ASAP);
        assert_eq!(label_key(&l2), "Sp2p(2,1:1)");
    }

    #[test]
    fn timed_send_label_key_appends_window_suffix() {
        let finite = Label::send_within(Model::P2p, 2, "x", Window::new(10, 20));
        assert_eq!(label_key(&finite), "Sp2p(2,1:x)@[10,20]");
        let unbounded = Label::send_within(Model::Asyn, 1, "x", Window::at_least(10));
        assert_eq!(label_key(&unbounded), "Sasyn(1,1:x)@[10,∞]");
    }

    #[test]
    fn window_participates_in_canonical_key() {
        // Two graphs differing only in a send's window are distinct graphs.
        let mut g = ExecutionGraph::new();
        g.add_event(
            0,
            Label::send_within(Model::P2p, 1, "x", Window::new(10, 20)),
        );
        let mut h = ExecutionGraph::new();
        h.add_event(
            0,
            Label::send_within(Model::P2p, 1, "x", Window::new(30, 40)),
        );
        assert_ne!(g.canonical_key(), h.canonical_key());

        // An untimed graph keys identically whether built via send or send_within(ASAP).
        let mut a = ExecutionGraph::new();
        a.add_event(0, Label::send(Model::P2p, 1, "x"));
        let mut b = ExecutionGraph::new();
        b.add_event(0, Label::send_within(Model::P2p, 1, "x", Window::ASAP));
        assert_eq!(a.canonical_key(), b.canonical_key());
    }

    #[test]
    fn send_window_accessor() {
        let mut g = ExecutionGraph::new();
        let s = g.add_event(
            0,
            Label::send_within(Model::P2p, 1, "x", Window::new(10, 20)),
        );
        let r = g.add_event(1, Label::recv(Pred::any()));
        assert_eq!(g.send_window(s), Some(Window::new(10, 20)));
        assert_eq!(g.send_window(r), None); // non-send
        assert_eq!(g.send_window(EventId::new(9, 9)), None); // missing event
    }

    #[test]
    fn read_bookkeeping_survives_transient_double_read() {
        // Regression: with a cached inverse map, set_rf(r2, Some(s)); set_rf(r2, None)
        // used to erase the fact that r1 still reads s.
        let mut g = ExecutionGraph::new();
        let s = g.add_event(0, Label::send(Model::P2p, 1, "1"));
        let r1 = g.add_event(1, Label::recv(Pred::any()));
        let r2 = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(r1, Some(s));
        g.set_rf(r2, Some(s)); // transient (ill-formed) double read
        g.set_rf(r2, None);
        assert!(g.is_read(s));
        assert!(g.unread_sends().is_empty());
    }
    fn assert_restored(g: &ExecutionGraph, before: &ExecutionGraph) {
        assert_eq!(g.canonical_key(), before.canonical_key());
        assert_eq!(g.num_threads(), before.num_threads());
        assert_eq!(g.next_stamp, before.next_stamp);
        assert_eq!(g.send_count, before.send_count);
        assert_eq!(g.backward_rf, before.backward_rf);
        assert_eq!(g.model_mask, before.model_mask);
        assert_eq!(
            g.porf_acyclic.load(Ordering::Relaxed),
            before.porf_acyclic.load(Ordering::Relaxed)
        );
        for event in g.iter_events() {
            assert_eq!(g.stamp(event), before.stamp(event));
        }
    }

    #[test]
    fn append_restore_preserves_nested_metadata_and_retained_snapshots() {
        let mut g = ExecutionGraph::new();
        let source = g.add_event(0, Label::send(Model::P2p, 1, "a"));
        g.add_event(1, Label::recv_nb(Pred::any()));
        let chosen = g.add_event(2, Label::nondet(["a", "b"]));
        g.set_nd(chosen, "a".into());
        assert!(g.is_porf_acyclic());
        let before = g.clone();

        let outer = g.checkpoint();
        let received = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(received, Some(source));
        let parent_snapshot = g.clone();
        let parent_key = parent_snapshot.canonical_key();

        // Adds an entirely new thread, including empty slots in between.
        let inner = g.checkpoint();
        let sent = g.add_event(5, Label::send(Model::Mbox, 0, "b"));
        let child_snapshot = g.clone();
        let child_key = child_snapshot.canonical_key();
        g.restore_append(inner, sent);
        assert_restored(&g, &parent_snapshot);
        assert_eq!(child_snapshot.canonical_key(), child_key);
        assert!(child_snapshot.contains(sent));

        // Appends into an existing shared row and changes the new annotation.
        let inner = g.checkpoint();
        let nondet = g.add_event(1, Label::nondet(["a", "b"]));
        g.set_nd(nondet, "b".into());
        let nondet_snapshot = g.clone();
        g.restore_append(inner, nondet);
        assert_restored(&g, &parent_snapshot);
        assert_eq!(nondet_snapshot.nd_value(nondet), Some(&"b".into()));

        g.restore_append(outer, received);
        assert_restored(&g, &before);
        assert_eq!(parent_snapshot.canonical_key(), parent_key);
        assert_eq!(parent_snapshot.reads_from(received), Some(source));
        assert_eq!(child_snapshot.canonical_key(), child_key);

        // Next append gets the exact original insertion stamp again.
        let checkpoint = g.checkpoint();
        let sent = g.add_event(0, Label::send(Model::Cd, 1, "c"));
        assert_eq!(g.stamp(sent), before.next_stamp);
        g.restore_append(checkpoint, sent);
        assert_restored(&g, &before);
    }

    #[test]
    fn append_restore_recovers_a_cached_negative_acyclicity_answer() {
        let mut g = ExecutionGraph::new();
        let receive = g.add_event(0, Label::recv(Pred::any()));
        let send = g.add_event(0, Label::send(Model::Asyn, 0, "a"));
        g.set_rf(receive, Some(send));
        assert!(!g.is_porf_acyclic());
        let before = g.clone();
        let checkpoint = g.checkpoint();
        let appended = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(appended, Some(send));
        assert!(!g.is_porf_acyclic());
        g.restore_append(checkpoint, appended);
        assert_restored(&g, &before);
        assert!(!g.is_porf_acyclic());
    }

    #[test]
    fn cached_models_match_surviving_send_labels() {
        let models = [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox];
        let mut g = ExecutionGraph::new();
        for (tid, &model) in models.iter().enumerate() {
            g.add_event(tid, Label::send(model, 0, "a"));
        }
        // Every subset is po-prefix-closed: one send per thread.
        for subset in 0..16 {
            let keep = g
                .iter_events()
                .filter(|e| subset & (1 << e.tid) != 0)
                .collect();
            let restricted = g.restrict(&keep);
            for model in models {
                assert_eq!(
                    restricted.uses_model(model),
                    restricted
                        .iter_sends()
                        .any(|s| restricted.send_model(s) == Some(model))
                );
            }
        }
    }
    #[test]
    fn forward_rf_matches_general_rf_for_every_older_source_and_bottom() {
        let mut prefix = ExecutionGraph::new();
        let first = prefix.add_event(0, Label::send(Model::P2p, 2, "a"));
        let middle = prefix.add_event(1, Label::recv(Pred::any()));
        let second = prefix.add_event(1, Label::send(Model::Cd, 2, "b"));
        prefix.set_rf(middle, Some(first));
        let receive = prefix.add_event(2, Label::recv_nb(Pred::any()));
        assert!(prefix.is_porf_acyclic());
        let mut fast = prefix.clone();
        let mut general = prefix.clone();
        for source in [
            Some(first),
            Some(second),
            None,
            None,
            Some(second),
            Some(first),
        ] {
            fast.set_rf_forward(receive, source);
            general.set_rf(receive, source);
            assert_eq!(fast.canonical_key(), general.canonical_key());
            assert_eq!(fast.reads_from(receive), source);
            assert_eq!(fast.backward_rf, general.backward_rf);
            assert_eq!(fast.is_porf_acyclic(), general.is_porf_acyclic());
            assert_eq!(
                fast.is_porf_acyclic(),
                fast.iter_events()
                    .all(|event| !fast.porf_prefix(event).contains(&event))
            );
            // The prefix has r1 ← s0; r2's additional read may transiently
            // double-read s0. Read bookkeeping must preserve the older reader.
            assert_eq!(fast.unread_sends(), general.unread_sends());
            assert!(fast.is_read(first));
        }
        assert_eq!(prefix.reads_from(receive), None); // COW snapshot unchanged
    }
    #[test]
    fn forward_rf_preserves_acyclicity_cache_with_backward_prefix_edges() {
        for cyclic in [false, true] {
            let mut g = ExecutionGraph::new();
            let previous = g.add_event(0, Label::recv_nb(Pred::any()));
            let send = g.add_event(usize::from(!cyclic), Label::send(Model::Asyn, 2, "a"));
            g.set_rf(previous, Some(send)); // later-stamped source
            assert_eq!(g.is_porf_acyclic(), !cyclic);
            let receive = g.add_event(2, Label::recv_nb(Pred::any()));
            let before = g.porf_acyclic.load(Ordering::Relaxed);
            let backward = g.backward_rf;
            for source in [Some(send), None, Some(send)] {
                g.set_rf_forward(receive, source);
                assert_eq!(g.porf_acyclic.load(Ordering::Relaxed), before);
                assert_eq!(g.backward_rf, backward);
                assert_eq!(
                    g.is_porf_acyclic(),
                    g.iter_events()
                        .all(|event| !g.porf_prefix(event).contains(&event))
                );
            }
        }
    }
    #[test]
    fn marks_grow_remove_reinsert_and_generation_do_not_leak_old_sources() {
        let mut graph = ExecutionGraph::new();
        let first = graph.add_event(0, Label::send(Model::Asyn, 1, "a"));
        let mut marks = Marks::default();
        marks.begin(&graph);
        assert!(marks.insert(first));
        assert!(marks.contains(first));
        assert!(marks.remove(first));
        assert!(!marks.remove(first));
        assert!(!marks.contains(first));
        assert!(marks.insert(first));
        assert!(!marks.insert(first));

        // New send cells are outside the original grid until explicitly grown.
        let later = graph.add_event(3, Label::send(Model::Asyn, 1, "b"));
        marks.grow(&graph);
        assert!(marks.contains(first));
        assert!(!marks.contains(later));
        assert!(marks.insert(later));
        assert!(marks.remove(later));
        assert!(marks.insert(later));
        marks.begin(&graph);
        assert!(!marks.contains(first));
        assert!(!marks.contains(later));
        assert!(!marks.remove(first));
        assert!(!marks.remove(later));
        assert!(marks.insert(later));
        assert!(marks.contains(later));
    }
    #[test]
    fn private_thread_cow_keeps_snapshots_immutable_across_concurrent_clone_and_drop() {
        use std::sync::Barrier;

        let mut graph = ExecutionGraph::new();
        let send = graph.add_event(0, Label::send(Model::Asyn, 1, "a"));
        let receive = graph.add_event(1, Label::recv_nb(Pred::any()));
        graph.set_rf(receive, Some(send));
        let oracle = graph.clone();
        let expected_key = oracle.canonical_key();
        let expected_stamps = oracle.events_by_stamp();
        let barrier = Arc::new(Barrier::new(2));
        std::thread::scope(|scope| {
            let rounds = if cfg!(miri) { 4 } else { 128 };
            let clone_rounds = if cfg!(miri) { 4 } else { 32 };
            for _ in 0..rounds {
                let snapshot = graph.clone();
                let worker_barrier = Arc::clone(&barrier);
                let expected_key = expected_key.clone();
                let expected_stamps = expected_stamps.clone();
                let worker = scope.spawn(move || {
                    worker_barrier.wait();
                    for _ in 0..clone_rounds {
                        let copy = snapshot.clone();
                        assert_eq!(copy.canonical_key(), expected_key);
                        assert_eq!(copy.events_by_stamp(), expected_stamps);
                        assert!(copy.is_porf_acyclic());
                        assert_eq!(copy.num_sends(), 1);
                    }
                });
                barrier.wait();
                // COW mutation races with cloning and dropping foreign snapshots.
                let checkpoint = graph.checkpoint();
                let appended = graph.add_event(1, Label::recv_nb(Pred::any()));
                graph.set_rf_forward(appended, Some(send));
                graph.restore_append(checkpoint, appended);
                worker.join().unwrap();
                assert_restored(&graph, &oracle);
            }
        });
        assert_eq!(oracle.canonical_key(), expected_key);
    }

    #[test]
    fn private_thread_cow_reclaims_unique_storage_after_foreign_owner_drop() {
        let mut graph = ExecutionGraph::new();
        graph.add_event(0, Label::send(Model::Asyn, 1, "a"));
        // Drop the last external owner on another thread. The following append
        // mutates unique storage without first joining that thread.
        let rounds = if cfg!(miri) { 4 } else { 64 };
        for _ in 0..rounds {
            let snapshot = graph.clone();
            let worker = std::thread::spawn(move || {
                assert_eq!(snapshot.thread_len(0), 1);
                assert_eq!(snapshot.num_sends(), 1);
                assert!(snapshot.label(EventId::new(0, 0)).is_send());
                drop(snapshot);
            });
            // Deliberately no join, barrier or acquire signal after the foreign
            // reads: standard Arc label ownership must protect the allocation.
            while Arc::strong_count(&graph.threads[0].labels) != 1 {
                std::thread::yield_now();
            }
            let before_key = graph.canonical_key();
            let before_stamp = graph.next_stamp;
            let checkpoint = graph.checkpoint();
            let appended = graph.add_event(0, Label::send(Model::Asyn, 1, "b"));
            assert_eq!(graph.stamp(appended), before_stamp);
            graph.restore_append(checkpoint, appended);
            assert_eq!(graph.canonical_key(), before_key);
            assert_eq!(graph.num_sends(), 1);
            assert_eq!(graph.backward_rf, 0);
            worker.join().unwrap();
        }
    }

    #[test]
    fn cuts_and_rf_mutations_share_labels_until_a_prefix_append() {
        let mut original = ExecutionGraph::new();
        let send = original.add_event(0, Label::send(Model::Asyn, 1, "first"));
        let receive = original.add_event(1, Label::recv_nb(Pred::any()));
        original.set_rf(receive, Some(send));
        let suffix = original.add_event(0, Label::send(Model::Asyn, 1, "discarded"));
        let choice = original.add_event(0, Label::nondet(["a", "b"]));
        original.set_nd(choice, "b".into());
        let original_key = original.canonical_key();

        let mut cut = original.restrict_to_lens(&[1, 1]);
        assert!(Arc::ptr_eq(
            &original.threads[0].labels,
            &cut.threads[0].labels
        ));
        assert_eq!(cut.threads[0].labels.len(), 3);
        assert_eq!(cut.thread_len(0), 1);
        assert!(!format!("{cut:?}").contains("discarded"));
        assert!(!cut.contains(suffix));
        cut.set_rf(receive, None);
        assert!(Arc::ptr_eq(
            &original.threads[1].labels,
            &cut.threads[1].labels
        ));
        assert_eq!(original.reads_from(receive), Some(send));
        assert_eq!(cut.reads_from(receive), None);

        let prefix_snapshot = cut.clone();
        let appended = cut.add_event(0, Label::send(Model::Asyn, 1, "replacement"));
        assert_eq!(appended, suffix);
        assert_eq!(cut.label(appended).val(), Some("replacement"));
        assert_eq!(cut.threads[0].labels.len(), 2);
        assert!(!Arc::ptr_eq(
            &original.threads[0].labels,
            &cut.threads[0].labels
        ));
        assert!(Arc::ptr_eq(
            &original.threads[0].labels,
            &prefix_snapshot.threads[0].labels
        ));
        assert_eq!(prefix_snapshot.thread_len(0), 1);
        assert_eq!(original.label(suffix).val(), Some("discarded"));
        assert_eq!(original.nd_value(choice), Some(&"b".into()));
        assert_eq!(original.canonical_key(), original_key);
    }

    #[test]
    fn kept_reachability_matches_materialized_prefix_cuts_and_rf_erasure() {
        let mut g = ExecutionGraph::new();
        let s0 = g.add_event(0, Label::send(Model::Asyn, 1, "a"));
        let r1 = g.add_event(1, Label::recv_nb(Pred::eq("a")));
        g.set_rf(r1, Some(s0));
        let s1 = g.add_event(1, Label::send(Model::Asyn, 2, "b"));
        let r2 = g.add_event(2, Label::recv_nb(Pred::eq("b")));
        g.set_rf(r2, Some(s1));
        let s2 = g.add_event(2, Label::send(Model::Asyn, 0, "c"));
        let r0 = g.add_event(0, Label::recv_nb(Pred::eq("c")));
        g.set_rf(r0, Some(s2));
        let r3 = g.add_event(3, Label::recv_nb(Pred::eq("d")));
        let s3 = g.add_event(4, Label::send(Model::Asyn, 3, "d"));
        g.set_rf(r3, Some(s3));
        assert!(g.is_porf_acyclic());
        let events = g.all_events();
        for encoded in 0..108 {
            let mut remaining = encoded;
            let mut lens = Vec::new();
            for tid in 0..g.num_threads() {
                let base = g.thread_len(tid) + 1;
                lens.push(remaining % base);
                remaining /= base;
            }
            let kept = |event: EventId| event.idx < lens[event.tid];
            let restricted = g.restrict_to_lens(&lens);
            for skip in [None, Some(r0), Some(r1), Some(r2), Some(r3)] {
                let mut reference = restricted.clone();
                if let Some(receive) = skip.filter(|&event| reference.contains(event)) {
                    reference.set_rf(receive, None);
                }
                for &from in &events {
                    for &to in &events {
                        let expected = reference.contains(from)
                            && reference.contains(to)
                            && reference.porf_reaches(from, to);
                        assert_eq!(
                            g.porf_reaches_kept(from, to, kept, skip),
                            expected,
                            "lens={lens:?} skip={skip:?} from={from:?} to={to:?}"
                        );
                    }
                }
            }
        }
        // A path in the original can disappear even while both endpoints survive.
        let lens = [1, 1, 2, 1, 1];
        assert!(g.porf_reaches(s0, s2));
        assert!(!g.porf_reaches_kept(s0, s2, |event| event.idx < lens[event.tid], None));
    }

    #[test]
    fn kind_masks_match_full_label_scans_across_word_boundary_cuts_and_restore() {
        fn check(g: &ExecutionGraph) {
            let mut all = Vec::new();
            let mut sends = Vec::new();
            let mut receives = Vec::new();
            for tid in 0..g.num_threads() {
                for idx in 0..g.thread_len(tid) {
                    let event = EventId::new(tid, idx);
                    all.push(event);
                    if g.label(event).is_send() {
                        sends.push(event);
                    }
                    if g.label(event).is_recv() {
                        receives.push(event);
                    }
                }
            }
            assert_eq!(g.iter_events().collect::<Vec<_>>(), all);
            assert_eq!(g.iter_sends().collect::<Vec<_>>(), sends);
            assert_eq!(g.iter_recvs().collect::<Vec<_>>(), receives);
        }

        let mut g = ExecutionGraph::new();
        check(&g);
        for idx in 0..83 {
            for tid in [1, 3, 6] {
                let label = match (idx + tid) % 5 {
                    0 | 4 => Label::send(Model::Asyn, 0, "message"),
                    1 => Label::recv_nb(Pred::any()),
                    2 => Label::nondet(["a", "b"]),
                    _ => Label::error("example"),
                };
                g.add_event(tid, label);
            }
        }
        check(&g);
        let original_key = g.canonical_key();
        for length in [0, 1, 2, 62, 63, 64, 65, 66, 83] {
            let lens = [0, length, 0, length, 0, 0, length];
            let mut cut = g.restrict_to_lens(&lens);
            check(&cut);
            let snapshot = cut.clone();
            for tid in [1, 3, 6] {
                let checkpoint = cut.checkpoint();
                let appended = cut.add_event(tid, Label::send(Model::Asyn, 0, "replacement"));
                check(&cut);
                check(&snapshot);
                cut.restore_append(checkpoint, appended);
                check(&cut);
                let checkpoint = cut.checkpoint();
                let appended = cut.add_event(tid, Label::recv_nb(Pred::any()));
                check(&cut);
                cut.restore_append(checkpoint, appended);
                check(&cut);
            }
            check(&snapshot);
            assert_eq!(cut.canonical_key(), snapshot.canonical_key());
        }
        check(&g);
        assert_eq!(g.canonical_key(), original_key);
    }

    #[test]
    fn compact_causal_prefix_matches_independent_traversal_and_fallback_domains() {
        fn reference(g: &ExecutionGraph, event: EventId) -> BTreeSet<EventId> {
            let mut result = BTreeSet::new();
            let mut work = VecDeque::new();
            if event.idx > 0 {
                work.push_back(EventId::new(event.tid, event.idx - 1));
            }
            if let Some(source) = g.reads_from(event) {
                work.push_back(source);
            }
            while let Some(event) = work.pop_front() {
                if !result.insert(event) {
                    continue;
                }
                if event.idx > 0 {
                    work.push_back(EventId::new(event.tid, event.idx - 1));
                }
                if let Some(source) = g.reads_from(event) {
                    work.push_back(source);
                }
            }
            result
        }
        fn check(g: &ExecutionGraph, event: EventId, compact: bool) {
            let expected = reference(g, event);
            let actual = g.causal_prefix(event);
            assert_eq!(matches!(&actual, CausalPrefix::Small(_)), compact);
            for tid in 0..6 {
                for idx in 0..70 {
                    let id = EventId::new(tid, idx);
                    assert_eq!(
                        actual.contains(&id),
                        expected.contains(&id),
                        "event={event:?} candidate={id:?}"
                    );
                }
            }
            assert_eq!(actual.into_tree(), expected);
            assert_eq!(g.porf_prefix(event), expected);
        }
        let mut seed = 0x219d_345f_a997_651bu64;
        let mut draw = |bound: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed as usize % bound
        };
        for _ in 0..96 {
            let mut g = ExecutionGraph::new();
            for _ in 0..32 {
                let tid = draw(4);
                let label = if draw(2) == 0 {
                    Label::send(Model::Asyn, draw(4), "value")
                } else {
                    Label::recv_nb(Pred::any())
                };
                g.add_event(tid, label);
            }
            let events = g.all_events();
            for receive in g.recvs() {
                if draw(4) != 0 {
                    g.set_rf(receive, Some(events[draw(events.len())]));
                }
            }
            // Backward RF edges and arbitrary causal cycles are intentional here.
            for &event in &events {
                check(&g, event, true);
            }
            let lens: Vec<_> = (0..g.num_threads())
                .map(|tid| draw(g.thread_len(tid) + 1))
                .collect();
            let cut = g.restrict_to_lens(&lens);
            for event in cut.iter_events() {
                check(&cut, event, true);
            }
        }
        let mut boundary = ExecutionGraph::new();
        for _ in 0..64 {
            boundary.add_event(3, Label::send(Model::Asyn, 0, "value"));
        }
        check(&boundary, EventId::new(3, 63), true);
        let large = boundary.add_event(3, Label::send(Model::Asyn, 0, "value"));
        check(&boundary, large, false);
        let mut many_threads = ExecutionGraph::new();
        let event = many_threads.add_event(4, Label::recv_nb(Pred::any()));
        check(&many_threads, event, false);
        let mut dangling = ExecutionGraph::new();
        let event = dangling.add_event(0, Label::recv_nb(Pred::any()));
        dangling.set_rf(event, Some(EventId::new(4, 0)));
        check(&dangling, event, false);
        dangling.set_rf(event, Some(EventId::new(0, 65)));
        check(&dangling, event, false);
        dangling.set_rf(event, Some(event));
        check(&dangling, event, true);
        assert!(dangling.causal_prefix(event).contains(&event));
    }

    #[test]
    fn packed_rf_preserves_all_coordinates_clone_cut_and_reused_slots() {
        assert_eq!(std::mem::size_of::<EventMeta>(), 32);
        let max = u32::MAX as usize;
        let sources = [
            EventId::new(0, 0),
            EventId::new(max, max - 2),
            EventId::new(max, max - 1),
            EventId::new(max, max),
            EventId::new(usize::MAX, 0),
            EventId::new(0, usize::MAX),
        ];
        assert_ne!(PackedRf::encode(Some(sources[0])), PackedRf::WIDE);
        assert_ne!(PackedRf::encode(Some(sources[1])), PackedRf::WIDE);
        assert_eq!(PackedRf::encode(Some(sources[2])), PackedRf::WIDE);
        assert_eq!(PackedRf::encode(Some(sources[3])), PackedRf::WIDE);
        let mut g = ExecutionGraph::new();
        let real = g.add_event(0, Label::send(Model::Asyn, 1, "message"));
        let receive = g.add_event(1, Label::recv_nb(Pred::any()));
        let tail = g.add_event(2, Label::send(Model::Asyn, 1, "tail"));
        for source in sources {
            g.set_rf(receive, Some(source));
            assert_eq!(g.reads_from(receive), Some(source));
            assert!(g
                .canonical_key()
                .contains(&format!("⟨{},{}⟩", source.tid, source.idx)));
            let snapshot = g.clone();
            let key = snapshot.canonical_key();
            let identity = g.restrict_to_lens(&[1, 1, 1]);
            assert_eq!(identity.reads_from(receive), Some(source));
            let cut = g.restrict_to_lens(&[1, 1, 0]);
            assert_eq!(
                cut.reads_from(receive),
                if source == real { Some(real) } else { None }
            );
            assert_eq!(cut.backward_rf, 0);
            assert_eq!(g.unread_sends().contains(&real), source != real);
            g.set_rf(receive, None);
            assert_eq!(g.reads_from(receive), None);
            assert!(g.threads[1].wide_rf.is_none());
            assert_eq!(snapshot.reads_from(receive), Some(source));
            assert_eq!(snapshot.canonical_key(), key);
            assert!(snapshot.contains(tail));
        }
        // Changing between two Wide encodings must not compare only their marker.
        g.reset_program_prefix_namespace(71);
        g.set_rf(receive, Some(sources[2]));
        g.set_program_prefix(receive, 101);
        let snapshot = g.clone();
        g.set_rf(receive, Some(sources[3]));
        assert_eq!(g.reads_from(receive), Some(sources[3]));
        assert_eq!(g.program_prefix(1), None);
        assert_eq!(snapshot.reads_from(receive), Some(sources[2]));
        assert_eq!(snapshot.program_prefix(1), Some(101));

        let checkpoint = g.checkpoint();
        let fresh = g.add_event(1, Label::recv_nb(Pred::any()));
        g.set_rf(fresh, Some(sources[3]));
        let with_fresh = g.clone();
        g.restore_append(checkpoint, fresh);
        assert!(!g.threads[1]
            .wide_rf
            .as_ref()
            .unwrap()
            .contains_key(&fresh.idx));
        assert_eq!(g.reads_from(receive), Some(sources[3]));
        assert_eq!(with_fresh.reads_from(fresh), Some(sources[3]));
        let checkpoint = g.checkpoint();
        let reused = g.add_event(1, Label::recv_nb(Pred::any()));
        assert_eq!(reused, fresh);
        assert_eq!(g.reads_from(reused), None);
        g.set_rf_forward(reused, Some(real));
        assert_eq!(g.reads_from(reused), Some(real));
        g.restore_append(checkpoint, reused);
        g.set_rf(receive, None);
        let checkpoint = g.checkpoint();
        let only = g.add_event(1, Label::recv_nb(Pred::any()));
        g.set_rf(only, Some(sources[3]));
        g.restore_append(checkpoint, only);
        assert!(g.threads[1].wide_rf.is_none());
    }

    #[test]
    fn same_payload_source_changes_keep_only_program_prefixes_not_rf_or_consistency() {
        let mut g = ExecutionGraph::new();
        let a = g.add_event(0, Label::send(Model::Asyn, 1, "same"));
        let b = g.add_event(0, Label::send(Model::Asyn, 1, "same"));
        let different = g.add_event(0, Label::send(Model::Asyn, 1, "different"));
        let receive = g.add_event(1, Label::recv_nb(Pred::any()));
        let suffix = g.add_event(1, Label::send(Model::Asyn, 0, "reply"));
        g.set_rf(receive, Some(a));
        g.reset_program_prefix_namespace(72);
        g.set_program_prefix(receive, 51);
        g.set_program_prefix(suffix, 52);
        let traces = crate::scheduler::traces_of(&g, 2);
        let key = g.canonical_key();
        assert!(g.is_porf_acyclic());
        g.set_rf(receive, Some(b));
        assert_eq!(g.reads_from(receive), Some(b));
        assert_eq!(g.program_prefix(1), Some(52));
        assert_eq!(g.stored(receive).program_prefix, 51);
        assert_eq!(crate::scheduler::traces_of(&g, 2), traces);
        assert_ne!(g.canonical_key(), key);
        assert!(!g.is_read(a));
        assert!(g.is_read(b));
        assert_eq!(g.porf_acyclic.load(Ordering::Relaxed), 0);
        g.set_rf(receive, Some(different));
        assert_eq!(g.stored(receive).program_prefix, 0);
        assert_eq!(g.stored(suffix).program_prefix, 0);

        let mut forward = ExecutionGraph::new();
        let a = forward.add_event(0, Label::send(Model::Asyn, 1, "same"));
        let b = forward.add_event(0, Label::send(Model::Asyn, 1, "same"));
        let receive = forward.add_event(1, Label::recv_nb(Pred::any()));
        forward.set_rf_forward(receive, Some(a));
        forward.reset_program_prefix_namespace(73);
        forward.set_program_prefix(receive, 61);
        forward.set_rf_forward(receive, Some(b));
        assert_eq!(forward.reads_from(receive), Some(b));
        assert_eq!(forward.program_prefix(1), Some(61));
        forward.set_rf_forward(receive, None);
        assert_eq!(forward.program_prefix(1), None);
    }
}
