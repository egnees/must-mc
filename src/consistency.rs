//! Well-formedness and the per-model consistency predicates (Definitions 3.3 to 3.8).
//!
//! `consistent(G)` is well-formedness and `consistent_M(G)` for every model `M` that a
//! send in `G` uses. The graph is never physically restricted to one model's events: the
//! model brackets inside `so` already select the sends of model `M`, while `porf` ranges
//! over the whole graph, so causal chains may pass through events of other models.

use std::cell::RefCell;

use crate::event::{EventId, Model};
use crate::graph::{ExecutionGraph, Marks, PooledMarks};

/// Per-thread reusable scratch buffers for the consistency predicates. One instance per
/// worker thread (no sharing, no locks); `consistent` is never re-entrant, so a single
/// borrow per call is safe.
#[derive(Default)]
struct Scratch {
    /// receives, for the nested `so` scans.
    recvs: Vec<EventId>,
    /// unread sends `G.US`.
    unread: Vec<EventId>,
    /// read sends, marked once per check so "is this send unread?" is O(1).
    read: Marks,
    /// receives reading a mbox send, with that send's node index (`consistent_mbox`).
    mbox_recvs: Vec<(EventId, u32)>,
    /// mbox sends, the nodes of the `consistent_mbox` digraph, in (tid, idx) order.
    nodes: Vec<EventId>,
    /// That digraph as a bit matrix: bit `to` of row `from` (see `consistent_mbox`).
    adj: Vec<u64>,
    /// DFS colours over the node indices.
    color: Vec<u8>,
    /// DFS stack of (node index, next successor index).
    dfs: Vec<(u32, u32)>,
    /// porf-prefix marks for the (C) edges.
    marks: Marks,
    /// Traversal stack for those prefix walks.
    stack: Vec<EventId>,
}

thread_local! {
    static SCRATCH: RefCell<Scratch> = RefCell::new(Scratch::default());
}

/// `consistent(G)` (Definition 3.8).
pub fn consistent(g: &ExecutionGraph) -> bool {
    well_formed(g) && models_consistent(g)
}

fn models_consistent(g: &ExecutionGraph) -> bool {
    let (mut p2p, mut cd, mut mbox) = (false, false, false);
    for s in g.iter_sends() {
        match g.send_model(s) {
            Some(Model::P2p) => p2p = true,
            Some(Model::Cd) => cd = true,
            Some(Model::Mbox) => mbox = true,
            // asyn adds nothing beyond well-formedness (Definition 3.4).
            Some(Model::Asyn) | None => {}
        }
    }
    (!p2p || consistent_p2p(g)) && (!cd || consistent_cd(g)) && (!mbox || consistent_mbox(g))
}

/// Well-formedness (Definition 3.3), minus the send/receive model-match clause (a
/// receive carries no model).
pub fn well_formed(g: &ExecutionGraph) -> bool {
    let clauses_1_to_4 = SCRATCH.with(|s| {
        let read = &mut s.borrow_mut().read;
        read.begin(g);
        for r in g.iter_recvs() {
            match g.reads_from(r) {
                // (1) only a non-blocking receive may read nothing.
                None => {
                    if g.label(r).blocking() != Some(false) {
                        return false;
                    }
                }
                // (4) rf links a send to a matching receive on the right thread; the
                // model-match part is dropped because a receive carries no model.
                Some(s) => {
                    if !g.contains(s) || !g.label(s).is_send() || !g.matches(s, r) {
                        return false;
                    }
                    // (3) every send is read at most once (2 is automatic: rf is stored per
                    // receive): marking the sources as they are seen catches a second reader
                    // on the spot, where sorting them cost an O(n log n) pass per check.
                    if !read.insert(s) {
                        return false;
                    }
                }
            }
        }
        true
    });
    // (5) porf is irreflexive: no causal cycle (a DFS over po ∪ rf).
    clauses_1_to_4 && g.is_porf_acyclic()
}

/// Incremental `consistent(G)` for a graph that is a consistent parent plus one freshly
/// added, `≤_G`-maximal receive `r` (with its rf already set). Returns exactly
/// `consistent(G)` but re-checks only the clauses `r` can violate.
///
/// Justification (Definitions 3.3, 3.5, 3.6 and the backward-revisit invariants):
/// * porf-acyclicity (well-formedness clause 5) is skipped: a maximal event has only
///   incoming porf edges (po from `r-1`, rf from its source) and no outgoing ones, so it
///   cannot lie on a cycle, and the parent was acyclic.
/// * "each send read ≤ once" can only break via the pair containing `r`, so we check just
///   that `r`'s source is not already read by another receive.
/// * the model so-clauses (b)/(c) can only gain obligations that mention `r`: `r` is always
///   the *later* receive `r2` in clause (c), and adding `r` does not perturb porf among the
///   older events. Only the model of the send `r` reads is relevant (a receive of a foreign
///   model is skipped by every other model's clauses).
///
/// This is NOT valid after a backward revisit (which points an earlier receive at a later
/// send and can create a cycle); those paths keep the full [`consistent`].
pub fn consistent_after_recv(g: &ExecutionGraph, r: EventId) -> bool {
    let mut read = PooledMarks::take();
    mark_read_sources(g, Some(r), &mut read);
    consistent_after_recv_with(g, r, &read)
}

/// Mark the rf sources of every receive of `g` except `skip` (whose rf the caller is about
/// to vary). One pass, reusable across a whole rf-source enumeration: which *other* sends
/// are read does not depend on what `skip` reads.
pub(crate) fn mark_read_sources(g: &ExecutionGraph, skip: Option<EventId>, read: &mut Marks) {
    read.begin(g);
    for rr in g.iter_recvs() {
        if Some(rr) == skip {
            continue;
        }
        if let Some(src) = g.reads_from(rr) {
            read.insert(src);
        }
    }
}

/// [`consistent_after_recv`] with the "which sends are already read" marks supplied by the
/// caller (built by [`mark_read_sources`] with `skip = Some(r)`).
///
/// `visit_recv` re-points one receive at every candidate source in turn; the marks are the
/// same for all of them, so hoisting this pass out of that loop takes an O(|E|) scan off
/// every single rf-choice — the most frequent operation in the whole search.
pub(crate) fn consistent_after_recv_with(g: &ExecutionGraph, r: EventId, read: &Marks) -> bool {
    debug_assert!(
        g.label(r).is_recv(),
        "consistent_after_recv target must be a receive"
    );
    // well-formedness, restricted to `r` (clauses 1/3/4; clause 5 skipped, clause 2 is
    // automatic).
    let s = match g.reads_from(r) {
        // (1) only a non-blocking receive may read nothing.
        None => return g.label(r).blocking() == Some(false),
        // (4) rf links a matching send on the right thread.
        Some(s) => {
            if !g.contains(s) || !g.label(s).is_send() || !g.matches(s, r) {
                return false;
            }
            // (3) `r` reading `s` must not make `s` read twice - i.e. `s` must not already
            // be read by one of the *other* receives, which is exactly the mark.
            if read.contains(s) {
                return false;
            }
            s
        }
    };
    // Only the model of the send `r` reads can gain an obligation involving `r`.
    match g.send_model(s) {
        Some(Model::P2p) => so_after_recv(g, r, s, Model::P2p, read),
        Some(Model::Cd) => so_after_recv(g, r, s, Model::Cd, read),
        // mbox is a global acyclicity check; adding an edge can close a cycle between
        // mailboxes, so fall back to the full (still-correct, `g` is well-formed) check.
        Some(Model::Mbox) => consistent_mbox(g),
        Some(Model::Asyn) | None => true,
    }
}

/// The so-clause half of [`consistent_after_recv`] for p2p/cd: clause (b) for the new
/// receive `r` (reading `s`), and clause (c) with `r` as the later receive `r2`.
fn so_after_recv(
    g: &ExecutionGraph,
    r: EventId,
    s: EventId,
    model: Model,
    read: &Marks,
) -> bool {
    let is_model = |e: EventId| g.send_model(e) == Some(model);
    let so = |a: EventId, b: EventId| {
        is_model(a)
            && is_model(b)
            && match model {
                Model::P2p => a.tid == b.tid && a.idx < b.idx,
                Model::Cd => g.porf_reaches(a, b),
                _ => false,
            }
    };
    {
        // `read` marks the sends read by receives other than `r` (see `mark_read_sources`),
        // which is exactly "not in G.US" for every send `u` this clause considers: `u` is
        // so-before `s`, hence never `s` itself, and `r` reads only `s`.

        // (b): no unread send u that is so-before s and matches r. Under p2p `so` holds only
        // for an earlier send of s's own thread, so the scan is that po-prefix rather than
        // every send in the graph; cd's `so` is porf, which is not thread-local.
        let scan_all = model != Model::P2p;
        let check_b = |u: EventId| !(so(u, s) && g.matches(u, r));
        let ok_b = if scan_all {
            g.iter_sends().all(|u| read.contains(u) || check_b(u))
        } else {
            (0..s.idx).all(|idx| {
                let u = EventId::new(s.tid, idx);
                !g.label(u).is_send() || read.contains(u) || check_b(u)
            })
        };
        if !ok_b {
            return false;
        }
        // (c): r is ≤_G-maximal, hence the later receive r2; pair it with each earlier
        // receive r1 in its own thread.
        for idx in 0..r.idx {
            let r1 = EventId::new(r.tid, idx);
            if !g.label(r1).is_recv() {
                continue;
            }
            let Some(s1) = g.reads_from(r1) else { continue };
            if so(s, s1) && g.matches(s, r1) {
                return false;
            }
        }
        true
    }
}

/// asyn (Definition 3.4): full asynchrony imposes nothing beyond well-formedness.
///
/// Assumes `well_formed(g)`; use [`consistent`] for the full check.
pub fn consistent_asyn(_g: &ExecutionGraph) -> bool {
    true
}

/// p2p (Definition 3.5): messages from one sender to one receiver arrive in send order.
///
/// Checks clauses (b) and (c) only; assumes `well_formed(g)` (clause (a)). Use
/// [`consistent`] for the full check: a standalone call on an ill-formed graph does not
/// implement the definition.
pub fn consistent_p2p(g: &ExecutionGraph) -> bool {
    consistent_so(g, Model::P2p)
}

/// cd (Definition 3.6): causally ordered messages to one receiver arrive in causal order.
///
/// Checks clauses (b) and (c) only; assumes `well_formed(g)` (clause (a)). Use
/// [`consistent`] for the full check.
pub fn consistent_cd(g: &ExecutionGraph) -> bool {
    consistent_so(g, Model::Cd)
}

/// Shared body of p2p and cd (Definitions 3.5 and 3.6): the two differ only in the base
/// of `so` (po for p2p, porf for cd).
///
/// `so` relates two sends of the model when the base relates them; every use here is
/// restricted to a common destination. That destination equality is supplied by
/// `matches(_, r)`, which forces the send's destination to be the receiving thread, and
/// the read send has that destination too, so two sends share a destination exactly when
/// the unread or earlier one also matches `r`. Value matching applies to whole (send,
/// receive) pairs, which is what `matches` checks.
fn consistent_so(g: &ExecutionGraph, model: Model) -> bool {
    let is_model = |e: EventId| g.send_model(e) == Some(model);
    let so = |a: EventId, b: EventId| {
        is_model(a)
            && is_model(b)
            && match model {
                Model::P2p => a.tid == b.tid && a.idx < b.idx,
                Model::Cd => g.porf_reaches(a, b),
                _ => false,
            }
    };

    SCRATCH.with(|s| {
        // Disjoint reusable buffers: receives (scanned in nested loops), unread sends, and
        // the read-source marks used to compute `unread`.
        let Scratch {
            read,
            recvs,
            unread,
            ..
        } = &mut *s.borrow_mut();

        recvs.clear();
        recvs.extend(g.iter_recvs());

        // `unread` = sends no receive reads (same set as `g.unread_sends()`), via the mark
        // grid rather than a sorted source list.
        read.begin(g);
        for &r in recvs.iter() {
            if let Some(src) = g.reads_from(r) {
                read.insert(src);
            }
        }
        unread.clear();
        unread.extend(g.iter_sends().filter(|&snd| !read.contains(snd)));

        // (b): no unread send u that matches r and is so-before the send s that r read.
        // For p2p only u's on s's own thread, po-before it, can be so-before s, so the
        // unread scan is narrowed to that prefix (cd's `so` is porf, so it keeps the
        // full scan).
        let p2p = model == Model::P2p;
        for &r in recvs.iter() {
            let Some(s) = g.reads_from(r) else { continue };
            if !is_model(s) {
                continue;
            }
            if p2p {
                for idx in 0..s.idx {
                    let u = EventId::new(s.tid, idx);
                    if !read.contains(u) && so(u, s) && g.matches(u, r) {
                        return false;
                    }
                }
            } else {
                for &u in unread.iter() {
                    if so(u, s) && g.matches(u, r) {
                        return false;
                    }
                }
            }
        }

        // (c): no receives r1 po-before r2 where rf(r2) is so-before rf(r1) and rf(r2) also
        // matches r1 - i.e. same-destination messages received out of order.
        for &r1 in recvs.iter() {
            let Some(s1) = g.reads_from(r1) else { continue };
            for &r2 in recvs.iter() {
                if r1.tid != r2.tid || r1.idx >= r2.idx {
                    continue; // need r1 po-before r2
                }
                let Some(s2) = g.reads_from(r2) else { continue };
                if so(s2, s1) && g.matches(s2, r1) {
                    return false;
                }
            }
        }
        true
    })
}

/// mbox (Definition 3.7): any two messages to one receiver arrive in send order.
///
/// Rather than enumerate total delivery orders, consistency is the acyclicity of a global
/// digraph on all mbox sends, adapting Di Giusto et al. (POPL 2023, Definition 4.2). A
/// cycle means no single enqueue timeline is compatible with the observed reads and
/// causality. The three edge kinds:
///   (A) a read send must be delivered before an unread send that matched its reader;
///   (B) delivery order to a mailbox follows the receive order within a thread;
///   (C) enqueue order respects causality across all mailboxes (porf of the full graph).
///       Without (C) the check degenerates to asyn and cannot be split per destination,
///       since the cycle may run between two different mailboxes.
///
/// Assumes `well_formed(g)`; use [`consistent`] for the full check.
pub fn consistent_mbox(g: &ExecutionGraph) -> bool {
    let is_mbox = |e: EventId| g.send_model(e) == Some(Model::Mbox);

    SCRATCH.with(|sc| {
        let Scratch {
            nodes,
            mbox_recvs,
            unread,
            read,
            adj,
            color,
            dfs,
            marks,
            stack,
            ..
        } = &mut *sc.borrow_mut();

        nodes.clear();
        nodes.extend(g.iter_sends().filter(|&s| is_mbox(s)));
        // No edge is ever a self-loop ((A) joins a read send to an unread one, (B) two
        // sends read by different receives, (C) excludes s = t), so fewer than two nodes
        // cannot form a cycle. This is the common case whenever a program uses mbox for
        // just one channel, and it skips the whole edge build.
        let k = nodes.len();
        if k < 2 {
            return true;
        }
        // Node index of a mbox send: `nodes` is in (tid, idx) order, so a binary search.
        let index_of = |e: EventId| nodes.binary_search(&e).ok();

        let words = k.div_ceil(64);
        adj.clear();
        adj.resize(k * words, 0);
        let mut link = |from: usize, to: usize| adj[from * words + to / 64] |= 1 << (to % 64);

        // Only the receives that read a mbox send take part in (A) and (B) - in a program
        // that uses mbox for one channel those are a handful, where every receive in the
        // graph used to be scanned (and pair-scanned) here. Each is kept with the node
        // index of the send it reads.
        mbox_recvs.clear();
        for r in g.iter_recvs() {
            if let Some(si) = g.reads_from(r).and_then(index_of) {
                mbox_recvs.push((r, si as u32));
            }
        }
        // Unread mbox sends: mark the read sources once, then keep the unmarked nodes.
        read.begin(g);
        for r in g.iter_recvs() {
            if let Some(src) = g.reads_from(r) {
                read.insert(src);
            }
        }
        unread.clear();
        unread.extend(nodes.iter().copied().filter(|&u| !read.contains(u)));

        // (A) s (read by r) -> u (unread, same destination, matches r).
        for &(r, si) in mbox_recvs.iter() {
            for &u in unread.iter() {
                if g.matches(u, r) {
                    let ui = index_of(u).expect("unread mbox send is a node");
                    link(si as usize, ui);
                }
            }
        }

        // (B) rf(r1) -> rf(r2) for r1 po-before r2 to the same mailbox, with rf(r2) matching r1.
        for &(r1, s1i) in mbox_recvs.iter() {
            for &(r2, s2i) in mbox_recvs.iter() {
                if r1.tid != r2.tid || r1.idx >= r2.idx {
                    continue;
                }
                if g.matches(nodes[s2i as usize], r1) {
                    link(s1i as usize, s2i as usize);
                }
            }
        }

        // (C) s -> t for any mbox sends where (s, t) is in porf of the full graph. One
        // porf walk per node (marking its prefix) rather than one per ordered pair.
        for (ti, &t) in nodes.iter().enumerate() {
            g.porf_prefix_into(t, marks, stack);
            for (si, &s) in nodes.iter().enumerate() {
                if si != ti && marks.contains(s) {
                    link(si, ti);
                }
            }
        }

        is_acyclic(k, words, adj, color, dfs)
    })
}

/// Acyclicity of the `k`-node digraph held as a bit matrix (`adj[from * words + to / 64]`),
/// by iterative three-colour DFS over caller-owned buffers.
fn is_acyclic(
    k: usize,
    words: usize,
    adj: &[u64],
    color: &mut Vec<u8>,
    stack: &mut Vec<(u32, u32)>,
) -> bool {
    const WHITE: u8 = 0;
    const GRAY: u8 = 1;
    const BLACK: u8 = 2;

    color.clear();
    color.resize(k, WHITE);
    stack.clear();

    for start in 0..k {
        if color[start] != WHITE {
            continue;
        }
        color[start] = GRAY;
        stack.push((start as u32, 0));
        while let Some(&(node, next)) = stack.last() {
            let (n, mut j) = (node as usize, next as usize);
            // Next successor of `n` at index >= j, scanning the row's bits.
            while j < k && adj[n * words + j / 64] >> (j % 64) & 1 == 0 {
                j += 1;
            }
            if j >= k {
                color[n] = BLACK;
                stack.pop();
                continue;
            }
            stack.last_mut().unwrap().1 = (j + 1) as u32;
            match color[j] {
                GRAY => return false, // back edge -> cycle
                WHITE => {
                    color[j] = GRAY;
                    stack.push((j as u32, 0));
                }
                _ => {}
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::{Label, Pred};

    #[test]
    fn empty_graph_is_consistent() {
        assert!(consistent(&ExecutionGraph::new()));
    }

    #[test]
    fn blocking_receive_reading_bottom_is_inconsistent() {
        let mut g = ExecutionGraph::new();
        let r = g.add_event(0, Label::recv(Pred::any()));
        g.set_rf(r, None);
        assert!(!well_formed(&g));
        assert!(!consistent(&g));
    }
}
