//! Well-formedness and the per-model consistency predicates.
//!
//! `consistent(G)` is well-formedness plus `consistent_M(G)` for every model `M` a send in
//! `G` uses. The graph is never physically restricted to one model's events: the model
//! brackets inside `so` already select that model's sends, while `porf` ranges over the
//! whole graph, so causal chains may pass through events of other models.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use crate::event::{EventId, Model};
use crate::graph::ExecutionGraph;

/// Per-thread reusable scratch buffers for the consistency predicates. One instance per
/// worker thread (no sharing, no locks); `consistent` is never re-entrant, so a single
/// borrow per call is safe.
#[derive(Default)]
struct Scratch {
    /// rf sources of receives, sorted to detect a send read more than once.
    sources: Vec<EventId>,
    /// receives, for the nested `so` scans.
    recvs: Vec<EventId>,
    /// unread sends `G.US`.
    unread: Vec<EventId>,
}

thread_local! {
    static SCRATCH: RefCell<Scratch> = RefCell::new(Scratch::default());
}

/// Full consistency: well-formed, and consistent under every model in use.
pub fn consistent(g: &ExecutionGraph) -> bool {
    well_formed(g) && models_consistent(g)
}

fn models_consistent(g: &ExecutionGraph) -> bool {
    let (mut p2p, mut cd, mut mbox) = (false, false, false);
    for s in g.sends() {
        match g.send_model(s) {
            Some(Model::P2p) => p2p = true,
            Some(Model::Cd) => cd = true,
            Some(Model::Mbox) => mbox = true,
            // asyn adds nothing beyond well-formedness.
            Some(Model::Asyn) | None => {}
        }
    }
    (!p2p || consistent_p2p(g)) && (!cd || consistent_cd(g)) && (!mbox || consistent_mbox(g))
}

/// Well-formedness, minus the send/receive model-match clause (a receive carries no model).
pub fn well_formed(g: &ExecutionGraph) -> bool {
    let rf_ok = SCRATCH.with(|s| {
        let sources = &mut s.borrow_mut().sources;
        sources.clear();
        for r in g.iter_recvs() {
            match g.reads_from(r) {
                // Reading nothing is only well-formed for a non-blocking receive.
                None => {
                    if g.label(r).blocking() != Some(false) {
                        return false;
                    }
                }
                // rf must link a matching send on the receiver's thread (the model-match
                // part is dropped because a receive carries no model).
                Some(s) => {
                    if !g.contains(s) || !g.label(s).is_send() || !g.matches(s, r) {
                        return false;
                    }
                    sources.push(s);
                }
            }
        }
        // Every send is read at most once (the reverse is automatic — rf holds one source
        // per receive): sort the sources and look for a duplicate.
        sources.sort_unstable();
        !sources.windows(2).any(|w| w[0] == w[1])
    });
    // porf must be irreflexive: no causal cycle.
    rf_ok && g.is_porf_acyclic()
}

/// Incremental `consistent(G)` for a graph that is a consistent parent plus one freshly
/// added, `≤_G`-maximal receive `r` (with its rf already set). Returns exactly
/// `consistent(G)` but re-checks only the clauses `r` can violate:
///
/// * porf-acyclicity is skipped — a maximal event has only incoming porf edges (po from its
///   predecessor, rf from its source) and none outgoing, so it cannot lie on a cycle, and
///   the parent was already acyclic.
/// * "each send is read at most once" can only break through the pair containing `r`, so we
///   check only that `r`'s source is not already read by another receive.
/// * the model ordering clauses can only gain obligations that mention `r`: it is always the
///   later of the two receives, and adding it does not reorder the older events. Only the
///   model of the send `r` reads matters.
///
/// This is NOT valid after a backward revisit (which points an earlier receive at a later
/// send and can create a cycle); those paths keep the full [`consistent`].
pub fn consistent_after_recv(g: &ExecutionGraph, r: EventId) -> bool {
    debug_assert!(
        g.label(r).is_recv(),
        "consistent_after_recv target must be a receive"
    );
    let s = match g.reads_from(r) {
        // Reading nothing is only well-formed for a non-blocking receive.
        None => return g.label(r).blocking() == Some(false),
        // rf must link a matching send on the receiver's thread...
        Some(s) => {
            if !g.contains(s) || !g.label(s).is_send() || !g.matches(s, r) {
                return false;
            }
            // ...and reading `s` must not make `s` read twice.
            if g.iter_recvs().any(|o| o != r && g.reads_from(o) == Some(s)) {
                return false;
            }
            s
        }
    };
    // Only the model of the send `r` reads can gain an obligation involving `r`.
    match g.send_model(s) {
        Some(Model::P2p) => so_after_recv(g, r, s, Model::P2p),
        Some(Model::Cd) => so_after_recv(g, r, s, Model::Cd),
        // mbox is a global acyclicity check; adding an edge can close a cycle between
        // mailboxes, so fall back to the full (still-correct, `g` is well-formed) check.
        Some(Model::Mbox) => consistent_mbox(g),
        Some(Model::Asyn) | None => true,
    }
}

/// The send-order half of [`consistent_after_recv`] for p2p/cd, checking only the two
/// obligations the new receive `r` (reading `s`) can create.
fn so_after_recv(g: &ExecutionGraph, r: EventId, s: EventId, model: Model) -> bool {
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
    SCRATCH.with(|sc| {
        // Read sources, sorted so "is this send unread?" is a binary search.
        let sources = &mut sc.borrow_mut().sources;
        sources.clear();
        sources.extend(g.iter_recvs().filter_map(|rr| g.reads_from(rr)));
        sources.sort_unstable();

        // `r` must read the earliest deliverable send: no unread matching send is so-before `s`.
        for u in g.iter_sends() {
            if sources.binary_search(&u).is_ok() {
                continue; // read, so not unread
            }
            if so(u, s) && g.matches(u, r) {
                return false;
            }
        }
        // `r` is the later receive: forbid taking a message out of order with each earlier
        // receive on its thread.
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
    })
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
        // `sources` as scratch to compute `unread`.
        let Scratch {
            sources,
            recvs,
            unread,
        } = &mut *s.borrow_mut();

        recvs.clear();
        recvs.extend(g.iter_recvs());

        // `unread` = sends no receive reads: collect the read sources, sort, keep sends not
        // present (same set as `g.unread_sends()`).
        sources.clear();
        sources.extend(g.iter_recvs().filter_map(|r| g.reads_from(r)));
        sources.sort_unstable();
        unread.clear();
        unread.extend(
            g.iter_sends()
                .filter(|snd| sources.binary_search(snd).is_err()),
        );

        // (b): no unread send u that matches r and is so-before the send s that r read.
        for &r in recvs.iter() {
            let Some(s) = g.reads_from(r) else { continue };
            if !is_model(s) {
                continue;
            }
            for &u in unread.iter() {
                if so(u, s) && g.matches(u, r) {
                    return false;
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
    let nodes: Vec<EventId> = g.sends().into_iter().filter(|&s| is_mbox(s)).collect();

    let mut adj: BTreeMap<EventId, BTreeSet<EventId>> = BTreeMap::new();

    // Receives are scanned three times below; materialise them once.
    let recvs = g.recvs();

    // (A) s (read by r) -> u (unread, same destination, matches r).
    let unread = g.unread_sends();
    for &r in &recvs {
        let Some(s) = g.reads_from(r) else { continue };
        if !is_mbox(s) {
            continue;
        }
        for &u in &unread {
            if is_mbox(u) && g.matches(u, r) {
                adj.entry(s).or_default().insert(u);
            }
        }
    }

    // (B) rf(r1) -> rf(r2) for r1 po-before r2 to the same mailbox, with rf(r2) matching r1.
    for &r1 in &recvs {
        let Some(s1) = g.reads_from(r1) else { continue };
        if !is_mbox(s1) {
            continue;
        }
        for &r2 in &recvs {
            if r1.tid != r2.tid || r1.idx >= r2.idx {
                continue;
            }
            let Some(s2) = g.reads_from(r2) else { continue };
            if is_mbox(s2) && g.matches(s2, r1) {
                adj.entry(s1).or_default().insert(s2);
            }
        }
    }

    // (C) s -> t for any mbox sends where (s, t) is in porf of the full graph.
    for &s in &nodes {
        for &t in &nodes {
            if s != t && g.porf_reaches(s, t) {
                adj.entry(s).or_default().insert(t);
            }
        }
    }

    is_acyclic(&nodes, &adj)
}

fn is_acyclic(nodes: &[EventId], adj: &BTreeMap<EventId, BTreeSet<EventId>>) -> bool {
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    fn visit(
        node: EventId,
        adj: &BTreeMap<EventId, BTreeSet<EventId>>,
        color: &mut BTreeMap<EventId, Color>,
    ) -> bool {
        color.insert(node, Color::Gray);
        if let Some(succ) = adj.get(&node) {
            for &n in succ {
                match color.get(&n).copied().unwrap_or(Color::White) {
                    Color::Gray => return false, // back edge -> cycle
                    Color::White => {
                        if !visit(n, adj, color) {
                            return false;
                        }
                    }
                    Color::Black => {}
                }
            }
        }
        color.insert(node, Color::Black);
        true
    }

    let mut color: BTreeMap<EventId, Color> = nodes.iter().map(|&n| (n, Color::White)).collect();
    for &n in nodes {
        if color[&n] == Color::White && !visit(n, adj, &mut color) {
            return false;
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
