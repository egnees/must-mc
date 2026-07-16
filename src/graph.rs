//! Execution graph: events plus program order (po) and the reads-from relation (rf),
//! with an insertion order over the events.
//!
//! `po` is exactly the order of events inside a thread vector. The insertion order is
//! materialised with a per-event stamp: insertion-order queries use `stamp`, while the
//! tid-then-idx order used by the tiebreaker uses `EventId`'s `Ord` directly.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::sync::Arc;

use crate::event::{EventId, Label, Model, Tid, Val};

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

    /// All events in `(tid, idx)` order, without allocating a `Vec`: the iterator
    /// counterpart of [`all_events`](Self::all_events).
    pub fn iter_events(&self) -> impl Iterator<Item = EventId> + '_ {
        self.threads
            .iter()
            .enumerate()
            .flat_map(|(tid, thread)| (0..thread.len()).map(move |idx| EventId::new(tid, idx)))
    }

    /// All events in `(tid, idx)` order.
    pub fn all_events(&self) -> Vec<EventId> {
        self.iter_events().collect()
    }

    /// Sends in `(tid, idx)` order, without allocating — the iterator counterpart of
    /// [`sends`](Self::sends) for the consistency predicates.
    pub fn iter_sends(&self) -> impl Iterator<Item = EventId> + '_ {
        self.iter_events().filter(move |&e| self.label(e).is_send())
    }

    /// Receives in `(tid, idx)` order, without allocating — the iterator counterpart of
    /// [`recvs`](Self::recvs).
    pub fn iter_recvs(&self) -> impl Iterator<Item = EventId> + '_ {
        self.iter_events().filter(move |&e| self.label(e).is_recv())
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

    /// Unread sends `G.US`: sends no receive reads.
    pub fn unread_sends(&self) -> Vec<EventId> {
        let read: BTreeSet<EventId> = self
            .iter_events()
            .filter_map(|e| self.stored(e).rf)
            .collect();
        self.sends()
            .into_iter()
            .filter(|e| !read.contains(e))
            .collect()
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

    /// Whether `(a, b)` is in `G.porf` (strict).
    pub fn porf_reaches(&self, a: EventId, b: EventId) -> bool {
        self.porf_prefix(b).contains(&a)
    }

    /// Whether `po` and `rf` together are acyclic, i.e. no event reaches itself. This is
    /// a well-formedness requirement.
    ///
    /// An iterative three-colour DFS over `po` and `rf`, following the (at most two)
    /// predecessors of each event and reporting a cycle on a back edge to an ancestor
    /// still on the stack. Iterative rather than recursive so deep graphs cannot overflow
    /// the call stack.
    pub fn is_porf_acyclic(&self) -> bool {
        // Colour per event: 0 = unseen, 1 = on the DFS stack, 2 = fully explored.
        let mut color: Vec<Vec<u8>> = self
            .threads
            .iter()
            .map(|thread| vec![0u8; thread.len()])
            .collect();
        // Explicit DFS stack of (event, next predecessor slot to try).
        let mut stack: Vec<(EventId, u8)> = Vec::new();

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

        let kept = |e: EventId| e.tid < new_len.len() && e.idx < new_len[e.tid];

        // Re-stamp: order survivors by old stamp, then assign 0..n.
        let mut survivors: Vec<EventId> = Vec::new();
        for (tid, &len) in new_len.iter().enumerate() {
            for idx in 0..len {
                survivors.push(EventId::new(tid, idx));
            }
        }
        survivors.sort_by_key(|&e| self.stamp(e));
        let new_stamp: BTreeMap<EventId, u64> = survivors
            .iter()
            .enumerate()
            .map(|(rank, &e)| (e, rank as u64))
            .collect();

        let mut threads: Vec<Arc<Vec<StoredEvent>>> = Vec::with_capacity(new_len.len());
        for (tid, &len) in new_len.iter().enumerate() {
            let mut thread = Vec::with_capacity(len);
            for idx in 0..len {
                let e = EventId::new(tid, idx);
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
                    stamp: new_stamp[&e],
                    rf,
                    nd: old.nd,
                });
            }
            threads.push(Arc::new(thread));
        }

        ExecutionGraph {
            threads,
            next_stamp: survivors.len() as u64,
        }
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
fn label_key(l: &Label) -> String {
    match l {
        Label::Send { model, dst, val } => {
            let v = crate::intern::resolve(*val);
            format!("S{model}({dst},{}:{v})", v.len())
        }
        Label::Recv { pred, blocking } => {
            let b = if *blocking { "b" } else { "nb" };
            format!("R{b}[{}:{}]", pred.repr().len(), pred.repr())
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
