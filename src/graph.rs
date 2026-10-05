//! Execution graph: events plus program order (po) and the reads-from relation (rf),
//! with an insertion order over the events.
//!
//! `po` is exactly the order of events inside a thread vector. The insertion order is
//! materialised with a per-event stamp: insertion-order queries use `stamp`, while the
//! tid-then-idx order used by the tiebreaker uses `EventId`'s `Ord` directly.

use std::cell::RefCell;
use std::collections::{BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::sync::Arc;

use crate::event::{EventId, Label, Model, Tid, Val, Window};

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

    fn next(&mut self) -> Option<EventId> {
        loop {
            let thread = self.g.threads.get(self.tid)?;
            if self.idx >= thread.len() {
                self.tid += 1;
                self.idx = 0;
                continue;
            }
            let ev = &thread[self.idx];
            let e = EventId::new(self.tid, self.idx);
            self.idx += 1;
            let wanted = match self.kind {
                Kind::All => true,
                Kind::Send => ev.label.is_send(),
                Kind::Recv => ev.label.is_recv(),
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

/// One event as stored in the graph: its label, its insertion stamp, and — inlined rather
/// than held in side maps — the receive's reads-from source and the nondet event's chosen
/// value. Inlining `rf`/`nd` keeps each query an O(1) field access and lets a graph clone
/// copy just the thread vectors.
#[derive(Clone, Debug)]
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

/// Stamp invariant: within each thread, stamps strictly increase with `idx`.
/// `add_event` appends with a growing counter, and `restrict` keeps po-prefixes while
/// preserving relative stamp order. Hence any stamp-downward-closed event set is
/// automatically po-prefix-closed per thread, which is what makes `restrict`'s keep
/// sets valid.
#[derive(Clone, Debug, Default)]
pub struct ExecutionGraph {
    /// `threads[t]` holds the events of thread `t` in program order; the vector
    /// index is the event's `idx`, so `po` is exactly the vector order. Each event carries
    /// its own `rf`/`nd` inline (see [`StoredEvent`]). No inverse (read-by) map is cached:
    /// `is_read`/`unread_sends` scan the events, which stays correct even through the
    /// transient double-read states that arise during exploration.
    ///
    /// Each thread's vector sits behind an `Arc` with copy-on-write. Cloning a graph shares
    /// the thread vectors (a refcount bump per thread); a mutation
    /// (`add_event`/`set_rf`/`set_nd`) copies only the one thread it touches, and only while
    /// that thread is still shared with another graph. This is what a child graph exploits:
    /// it differs from its parent by a single appended event in one thread.
    threads: Vec<Arc<Vec<StoredEvent>>>,
    /// Monotonic insertion counter; the next added event gets this stamp.
    next_stamp: u64,
}

impl ExecutionGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn num_threads(&self) -> usize {
        self.threads.len()
    }

    pub fn thread_len(&self, tid: Tid) -> usize {
        self.threads.get(tid).map_or(0, |t| t.len())
    }

    /// Whether `e` denotes an event present in the graph.
    pub fn contains(&self, e: EventId) -> bool {
        e.idx < self.thread_len(e.tid)
    }

    fn stored(&self, e: EventId) -> &StoredEvent {
        &self.threads[e.tid][e.idx]
    }

    fn stored_mut(&mut self, e: EventId) -> &mut StoredEvent {
        // `make_mut` copies this thread's vector only while it is still shared; once
        // unique, repeated mutations are in place.
        &mut Arc::make_mut(&mut self.threads[e.tid])[e.idx]
    }

    pub fn label(&self, e: EventId) -> &Label {
        &self.stored(e).label
    }

    pub fn stamp(&self, e: EventId) -> u64 {
        self.stored(e).stamp
    }

    /// Add `label` as the latest event (in insertion order) of thread `tid`; returns its id.
    pub fn add_event(&mut self, tid: Tid, label: Label) -> EventId {
        if tid >= self.threads.len() {
            self.threads.resize_with(tid + 1, || Arc::new(Vec::new()));
        }
        let idx = self.threads[tid].len();
        let stamp = self.next_stamp;
        self.next_stamp += 1;
        Arc::make_mut(&mut self.threads[tid]).push(StoredEvent {
            label,
            stamp,
            rf: None,
            nd: None,
        });
        EventId::new(tid, idx)
    }

    /// Point receive `recv` at source `src` (`None` means it reads nothing), dropping any
    /// previous edge.
    pub fn set_rf(&mut self, recv: EventId, src: Option<EventId>) {
        debug_assert!(
            self.contains(recv) && self.label(recv).is_recv(),
            "set_rf target must be an existing receive"
        );
        self.stored_mut(recv).rf = src;
    }

    /// Source read by `r`: `Some(send)`, or `None` for nothing read.
    ///
    /// "No rf assigned yet" and an explicit "reads nothing" are not distinguished; both
    /// are `None`. The explorer calls `set_rf` immediately after adding a receive, so no
    /// receive ever reaches a consistency check with an unassigned rf.
    pub fn reads_from(&self, r: EventId) -> Option<EventId> {
        if self.contains(r) {
            self.stored(r).rf
        } else {
            None
        }
    }

    /// Whether `r` reads nothing (explicit, or no source assigned).
    pub fn reads_bottom(&self, r: EventId) -> bool {
        self.reads_from(r).is_none()
    }

    /// Whether send `s` is read by some receive. Scans events (non-receives carry `rf =
    /// None`, so they never match); no inverse map is kept.
    pub fn is_read(&self, s: EventId) -> bool {
        self.iter_events().any(|e| self.stored(e).rf == Some(s))
    }

    /// Assign the chosen value `v` to nondet event `e` (Algorithm 1, line 6), replacing
    /// any previous choice.
    pub fn set_nd(&mut self, e: EventId, v: Val) {
        debug_assert!(
            self.contains(e) && self.label(e).is_nondet(),
            "set_nd target must be an existing nondet event"
        );
        self.stored_mut(e).nd = Some(v);
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
        self.all_events()
            .into_iter()
            .filter(|&e| self.label(e).is_send())
            .collect()
    }

    pub fn recvs(&self) -> Vec<EventId> {
        self.all_events()
            .into_iter()
            .filter(|&e| self.label(e).is_recv())
            .collect()
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
                if let Some(src) = self.stored(e).rf {
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

    /// Whether `po` and `rf` together are acyclic, i.e. no event reaches itself. This is
    /// a well-formedness requirement.
    ///
    /// An iterative three-colour DFS over `po` and `rf`, following the (at most two)
    /// predecessors of each event and reporting a cycle on a back edge to an ancestor
    /// still on the stack. Iterative rather than recursive so deep graphs cannot overflow
    /// the call stack.
    pub fn is_porf_acyclic(&self) -> bool {
        GSCRATCH.with(|sc| {
            let GraphScratch {
                color,
                acyclic_stack: stack,
                ..
            } = &mut *sc.borrow_mut();
            self.porf_acyclic_with(color, stack)
        })
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
        // its own stamp — a clone (a refcount bump per thread) is the same graph for far
        // less work. Whole classes of `Previous` cuts delete nothing at all.
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
            for tid in 0..self.threads.len() {
                for idx in 0..len_of(tid) {
                    rank[self.threads[tid][idx].stamp as usize] = 0; // marked as surviving
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

            let mut threads: Vec<Arc<Vec<StoredEvent>>> = Vec::with_capacity(self.threads.len());
            for tid in 0..self.threads.len() {
                let len = len_of(tid);
                // A thread that loses no event, whose events all predate the cut (so their
                // stamps are unchanged) and whose receives all still find their source, is
                // bit-for-bit the old thread: share it instead of rebuilding (a refcount
                // bump against a full copy of every event).
                let unchanged = len == self.threads[tid].len()
                    && self.threads[tid]
                        .last()
                        .is_none_or(|ev| ev.stamp < cut_from)
                    && self.threads[tid].iter().all(|ev| ev.rf.is_none_or(kept));
                if unchanged {
                    threads.push(Arc::clone(&self.threads[tid]));
                    continue;
                }
                let mut thread = Vec::with_capacity(len);
                for idx in 0..len {
                    let old = &self.threads[tid][idx];
                    // Carry `rf` forward, normalizing a source that did not survive to ⊥
                    // (well-formedness later rejects that for a blocking receive). idx is
                    // preserved by the cut, so a kept source keeps the same EventId. "Reading
                    // nothing" and "unassigned" are both `None`, exactly as `reads_from` treats
                    // them. `nd` is carried verbatim (idx-keyed choices stay valid).
                    let rf = match old.rf {
                        Some(s) if kept(s) => Some(s),
                        _ => None,
                    };
                    thread.push(StoredEvent {
                        label: old.label.clone(),
                        stamp: rank[old.stamp as usize],
                        rf,
                        nd: old.nd,
                    });
                }
                threads.push(Arc::new(thread));
            }

            ExecutionGraph {
                threads,
                next_stamp: next,
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
            for ev in thread.iter() {
                let _ = write!(out, " {}", label_key(&ev.label));
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
}
