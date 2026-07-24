//! Backward revisits and the revisiting condition.
//!
//! When a send `e` has just been added (≤_G-maximal), it may become the source of an
//! earlier receive `r`. `Must` explores that (`rf(r) := e`) only from the canonical source
//! graph — the one built with no prior revisit, each non-blocking receive reading nothing,
//! each nondet at its minimum, and each blocking receive reading its deterministic
//! tiebreaker. `RevisitCondition` is exactly that canonicity test.

use std::collections::BTreeSet;

use crate::consistency::consistent;
use crate::event::{EventId, Label};
use crate::graph::ExecutionGraph;
use crate::observer::Observer;
use crate::program::Program;

use super::Explorer;

impl<P: Program, O: Observer> Explorer<'_, P, O> {
    /// For every revisitable receive `r`, delete the events added after it (except `e`'s
    /// causal prefix), and — if every deleted event and `r` itself satisfy `RevisitCondition`
    /// — explore the graph where `r` reads `e`.
    pub(crate) fn backward_revisits(&mut self, first: &mut bool, g: &ExecutionGraph, e: EventId) {
        // e's porf-prefix is reused by the candidate filter, `Deleted`, and every
        // `Previous`, so compute it once.
        let porf_e = g.porf_prefix(e);

        // Candidates: receives r that e matches and that are not porf-before e.
        for r in g.recvs() {
            if self.stopping() {
                return;
            }
            if !g.matches(e, r) || porf_e.contains(&r) {
                continue;
            }

            let deleted = deleted_set(g, r, &porf_e);

            // Check RevisitCondition for every e' in Deleted plus {r}. Deleted already
            // contains e (trivially passing); r is added explicitly, and the `chain(once(&r))`
            // is load-bearing: dropping it lets a revisit whose r does not read its tiebreaker
            // slip through, duplicating graphs (e.g. ns+r(3) under priorities [0,1,3,2] would
            // explore 4 executions instead of 3).
            let all_ok = deleted
                .iter()
                .chain(std::iter::once(&r))
                .all(|&ep| self.revisit_condition(g, ep, &porf_e));

            if !all_ok {
                self.observer.on_revisit_rejected(g, r, e);
                // Keep scanning other candidates - never `break`: the monotonicity that
                // would justify an early exit is unproven for the tiebreaker.
                continue;
            }

            // Restrict to G.E \ (Deleted \ {e}), then set rf(r) := e AFTER the cut. e stays
            // in the graph (it is in Deleted but must survive) and remains ≤_G-maximal.
            let mut keep: BTreeSet<EventId> = g.all_events().into_iter().collect();
            for &d in &deleted {
                if d != e {
                    keep.remove(&d);
                }
            }
            let mut g2 = g.restrict(&keep);
            g2.set_rf(r, Some(e));

            self.observer.on_backward_revisit(g, r, e, &deleted);
            self.branch_if_consistent(first, &g2);
        }
    }

    /// `RevisitCondition(G, e', s)`, where `porf_s` is the precomputed porf-prefix of the
    /// revisiting send `s` (the only way `s` enters the condition, via `Previous`).
    fn revisit_condition(
        &self,
        g: &ExecutionGraph,
        ep: EventId,
        porf_s: &BTreeSet<EventId>,
    ) -> bool {
        match g.label(ep) {
            // A non-blocking receive is canonical iff it reads bottom.
            Label::Recv {
                blocking: false, ..
            } => g.reads_bottom(ep),

            // A blocking receive is canonical iff it reads the tiebreaker send picked on
            // G|_Previous (NOT on the full G).
            Label::Recv { blocking: true, .. } => {
                let previous = previous_set(g, ep, porf_s);
                let h = g.restrict(&previous);
                g.reads_from(ep) == get_cons_tiebreaker(&h, ep)
            }

            // A nondet event is canonical iff it chose the minimum of its option set. This is
            // what keeps a backward revisit firing only from the unique canonical source
            // graph, in which every nondet sits at its minimum. Minimum by the *resolved
            // string* (never the nondeterministic `Sym` id), matching `Label::nondet`'s sort;
            // `min_by` (not `set.first()`) so canonicity holds even if a set reaches here
            // unsorted.
            Label::Nondet { set } => {
                let min = set
                    .iter()
                    .min_by(|a, b| crate::intern::resolve(**a).cmp(crate::intern::resolve(**b)));
                g.nd_value(ep) == min
            }

            // Any non-receive (send / error) is canonical iff no receive in Previous reads it
            // — i.e. it never itself backward-revisited an earlier receive (deleting it would
            // undo that revisit). Nondet is handled by its own arm above, so this covers only
            // sends and errors.
            Label::Send { .. } | Label::Error { .. } => {
                let previous = previous_set(g, ep, porf_s);
                !previous
                    .iter()
                    .any(|&rp| g.label(rp).is_recv() && g.reads_from(rp) == Some(ep))
            }
        }
    }
}

/// `Deleted = { e' in G.E | r <_G e' and (e', s) not in G.porf }`, with `porf_s` the
/// precomputed porf-prefix of `s`. Strict `<_G`; `s`'s porf-prefix is preserved. `s` itself
/// is included (it is ≤_G-maximal and not in its own porf-prefix), but the caller keeps it
/// in the graph.
fn deleted_set(g: &ExecutionGraph, r: EventId, porf_s: &BTreeSet<EventId>) -> BTreeSet<EventId> {
    let sr = g.stamp(r);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) > sr && !porf_s.contains(&x))
        .collect()
}

/// `Previous = { e' in G.E | e' ≤_G e or (e', s) in G.porf }`, with `porf_s` the precomputed
/// porf-prefix of the revisiting send `s`. Non-strict `≤_G` (so `e` itself is in Previous),
/// and the porf part is strict up to `s`. This encodes "as of when e was added": from the
/// future, e sees only s's porf-prefix, which is guaranteed to remain. The set is
/// po-prefix-closed (stamp-downward within each thread plus a porf-prefix), so `restrict`
/// accepts it as a keep set.
fn previous_set(g: &ExecutionGraph, e: EventId, porf_s: &BTreeSet<EventId>) -> BTreeSet<EventId> {
    let se = g.stamp(e);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) <= se || porf_s.contains(&x))
        .collect()
}

/// `GetConsTiebreaker(H, e)`, where `H = G|_Previous` and `e` is the blocking receive under
/// test. Returns the deterministic send `e` should read, or `None` if no consistent source
/// exists (then the revisit is rejected - no panic).
///
/// The function depends only on `(E, po, rf\{e}, e)` of `H`, never on stamps or container
/// order:
///   1. drop `e`'s own rf edge, AND
///   2. keep only sends unread by receives other than `e` (the `rp != e` filter).
///
/// Steps 1 and 2 are two independent guards for the same invariant "the send `e` currently
/// reads must remain a candidate" - do not remove one trusting the other. If step 1 is
/// dropped, `e`'s source stays marked as read (by `e`) and is excluded, so the tiebreaker
/// almost never equals `rf(e)` and revisits die (s+s+r with T1,T3 first would give 1
/// execution instead of 2). If step 2 is dropped, a send legitimately read by another
/// receive would wrongly become a candidate. Both are needed.
///
///   3. keep every remaining send that matches `e` and that it is consistent for `e` to
///      read; return the `(tid, idx)`-minimal such send.
pub fn get_cons_tiebreaker(h: &ExecutionGraph, e: EventId) -> Option<EventId> {
    let mut hp = h.clone();
    hp.set_rf(e, None); // guard 1: remove e's own rf edge

    let mut best: Option<EventId> = None;
    for s in hp.sends() {
        if !hp.matches(s, e) {
            continue;
        }
        // guard 2: unread by any receive other than e.
        let read_by_other = hp
            .recvs()
            .into_iter()
            .any(|rp| rp != e && hp.reads_from(rp) == Some(s));
        if read_by_other {
            continue;
        }
        // Consistent for e to read s.
        let mut trial = hp.clone();
        trial.set_rf(e, Some(s));
        if !consistent(&trial) {
            continue;
        }
        // (tid, idx)-minimal wins (EventId's Ord is exactly (tid, idx)).
        best = Some(best.map_or(s, |b| b.min(s)));
    }
    best
}
