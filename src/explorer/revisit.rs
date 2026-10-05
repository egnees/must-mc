//! Backward revisits and the revisiting condition (Algorithm 1, lines 10-13, 17-22).
//!
//! When a send `e` has just been added (<=G-maximal), it may become the source of an
//! earlier receive `r`. `Must` explores that (`rf(r) := e`) only from the canonical source
//! graph - the one built with no prior revisit, each non-blocking receive reading nothing,
//! each nondet at `min(S)`, and each blocking receive reading its deterministic tiebreaker.
//! `RevisitCondition` is exactly that canonicity test.

use std::cell::RefCell;
use std::collections::BTreeSet;

use super::source_order::SourceOrder;
use crate::consistency::consistent;
use crate::event::{EventId, Label, Val};
use crate::graph::ExecutionGraph;
use crate::observer::Observer;
use crate::program::Program;

use super::Explorer;

thread_local! {
    /// Per-thread keep-lengths for [`restrict_prefix`], reused across cuts.
    static LENS: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

/// `G|_keep` for a keep set described by a per-event predicate: each thread keeps the
/// maximal po-prefix whose events all satisfy `pred`.
///
/// Every keep set the revisit path cuts with (`Previous`, and `E \ (Deleted \ {e})`) is a
/// union of a stamp-downward set and a porf-prefix, so it is po-prefix-closed and is fully
/// described by those lengths — which is what lets the cut skip materialising the set at
/// all (the `BTreeSet` form was `|E|` tree inserts per candidate revisit). The debug
/// assertion re-checks the prefix-closedness that [`ExecutionGraph::restrict`] asserts.
fn restrict_prefix(g: &ExecutionGraph, pred: impl Fn(EventId) -> bool) -> ExecutionGraph {
    LENS.with(|l| {
        let lens = &mut *l.borrow_mut();
        lens.clear();
        for tid in 0..g.num_threads() {
            let len = g.thread_len(tid);
            let mut k = 0;
            while k < len && pred(EventId::new(tid, k)) {
                k += 1;
            }
            debug_assert!(
                (k + 1..len).all(|j| !pred(EventId::new(tid, j))),
                "restrict expects a po-prefix-closed keep set"
            );
            lens.push(k);
        }
        g.restrict_to_lens(lens)
    })
}

/// `G|_Previous` for [`previous_set`]'s set, cut through [`restrict_prefix`] instead of
/// through a materialised `BTreeSet` (same graph, same stamps).
pub(super) fn restrict_previous(
    g: &ExecutionGraph,
    e: EventId,
    porf_s: &BTreeSet<EventId>,
) -> ExecutionGraph {
    let se = g.stamp(e);
    restrict_prefix(g, |x| g.stamp(x) <= se || porf_s.contains(&x))
}

impl<P: Program, O: Observer> Explorer<'_, P, O> {
    /// lines 10-13: for every revisitable receive `r`, delete the events added after it
    /// (bar `e`'s causal prefix), and - if every deleted event and `r` itself satisfy
    /// `RevisitCondition` - explore the graph where `r` reads `e`.
    pub(crate) fn backward_revisits(&mut self, first: &mut bool, g: &ExecutionGraph, e: EventId) {
        // e's porf-prefix is reused by the candidate filter, `Deleted`, and every
        // `Previous`, so compute it once.
        let porf_e = g.porf_prefix(e);

        // line 10: candidates r with matches(e, r) and no porf path r -> e.
        for r in g.iter_recvs() {
            if self.stopping() {
                return;
            }
            if !g.matches(e, r) || porf_e.contains(&r) {
                continue;
            }

            // line 13 (hoisted): restrict to G.E \ (Deleted \ {e}), then rf(r) := e AFTER the
            // cut. e stays in the graph (it is in Deleted but must survive) and remains
            // <=G-maximal.
            //
            // B-0 (C1_HARDENING_SPEC §B.5 / §B.3 "про (c5)"): `g2` — hence both its consistency
            // and its T-GATE verdict — is a function of `(g, r, e)` alone; it does **not** depend
            // on the `e'` the RevisitCondition loop ranges over (B1.b(3)). Those two tests are
            // therefore common factors of the line-12 ∧ line-13 conjunction and are pulled in
            // front of the loop. The conjunction is unchanged; what disappears is every
            // *viability-oracle* call (the nondet arm of [`Self::revisit_condition`], and from
            // step 2 on its blocking-receive arm too) spent on a revisit that the gate or
            // consistency would have discarded anyway. Observer bookkeeping shifts accordingly —
            // a revisit whose `g2` is inconsistent now reports `on_inconsistent` instead of
            // `on_backward_revisit`, and a gate-rejected one no longer competes with
            // `on_revisit_rejected` for the same event (documented ФАКТ A2.1b).
            //
            // `Deleted = { x | r <G x and (x, e) ∉ porf }`, so the keep set is its
            // complement plus `e`: `stamp(x) <= stamp(r) or x ∈ porf(e) or x = e`. Stated
            // that way the cut needs no set at all (see [`restrict_prefix`]), and
            // `deleted_set` itself is deferred below to the survivors of the two rejection
            // tests — it is a pure function of `(g, r, porf_e)`, so nothing else moves.
            let sr = g.stamp(r);
            let mut g2 = restrict_prefix(g, |x| g.stamp(x) <= sr || porf_e.contains(&x) || x == e);
            g2.set_rf(r, Some(e));

            // line 13's `VisitIfConsistent`, evaluated here rather than at the recursion (so the
            // gate below never runs on an inconsistent graph — a blocking receive reading ⊥ has
            // no well-formed time system). `branch` below is the raw form, so consistency is
            // still tested exactly once per revisit.
            if !consistent(&g2) {
                self.observer.on_inconsistent(&g2);
                continue;
            }

            // T-GATE (T2_PLAN §2c, line 13): under the eager-time predicate a revisit that passes
            // `RevisitCondition` is still pruned when its *obligatory* continuation is
            // eager-infeasible. The right object is not `g2` alone (which the predicate already
            // accepted as feasible) but its forced-closure — `g2` plus every event the policy is
            // forced to re-add without a genuine rf-fork. The refuted-L3 counterexample:
            // `forced_closure(G′) = G′ + rg←g + m` is infeasible, so `s → r` is rejected here.
            // [`gate_feasible`] is the C1-safe form: it trusts the forced-closure verdict only
            // when the closure is exact, else falls back to raw `check(g2)` (see its docs).
            //
            // Ladder (`C1_HARDENING_SPEC` §D.4): T-GATE is the level-4 rung — at levels 2/3 the
            // revisit is taken whenever `RevisitCondition` and consistency allow it, so a
            // realizable terminal the gate might have cut off still surfaces (dropping a pruner
            // only adds branches, M2 §0.2).
            if self.time_predicate
                && self.time_level >= 4
                && !crate::time::gate_feasible_cached(
                    &g2,
                    self.program,
                    &self.priorities,
                    &mut self.viable_memo,
                )
            {
                self.observer.on_forced_closure_pruned(&g2, r, e);
                continue;
            }

            // line 12: check RevisitCondition for every e' in Deleted plus {r}. Deleted
            // already contains e (trivially passing), and r is added explicitly - the
            // explicit `r` iteration is load-bearing: dropping it lets a revisit whose r does
            // not read its tiebreaker slip through, duplicating graphs (e.g. ns+r(3) under
            // priorities [0,1,3,2] would explore 4 instead of 3). Imperative (not `.all()`)
            // because the nondet arm's viable oracle needs `&mut self` for its memo.
            // `Deleted` is walked, not built: the set object is only needed by the observer
            // on the accepted path below, and the predicate is the same one the keep-lengths
            // above use.
            self.observer.on_revisit_candidate(g, r, e, &g2);
            let mut all_ok = true;
            for ep in g
                .iter_events()
                .filter(|&x| g.stamp(x) > sr && !porf_e.contains(&x))
                .chain(std::iter::once(r))
            {
                if !self.revisit_condition(g, ep, &porf_e, e) {
                    self.observer.on_revisit_arm_rejected(g, r, e, &g2, ep);
                    all_ok = false;
                    break;
                }
            }

            if !all_ok {
                self.observer.on_revisit_rejected(g, r, e);
                // Keep scanning other candidates - never `break`: the monotonicity that
                // would justify an early exit is unproven for the tiebreaker.
                continue;
            }

            // A repairing send can make every old holder fail the viability oracle even
            // though its rewritten target is feasible. PASS then admits several holders.
            // Reject one only when a bounded replay proves that an all-minimum owner
            // reaches the identical target, including insertion stamps. That owner's
            // path is forward-only and its final canonical arms are unconditional minima,
            // so this rejection cannot remove its replacement. Unsupported/over-budget
            // cases retain the existing decision; this is not a general T2 proof.
            if self.time_predicate && self.time_level >= 4 && !self.canon_free {
                if let Some(owner) = super::repair_owner::certify_forward_minimum_owner(
                    self.program,
                    &self.priorities,
                    g,
                    r,
                    e,
                    &g2,
                    256,
                ) {
                    self.observer.on_revisit_owner_certified(
                        g,
                        r,
                        e,
                        &owner.host,
                        owner.replay_events,
                    );
                    self.observer.on_revisit_arm_rejected(g, r, e, &g2, r);
                    self.observer.on_revisit_rejected(g, r, e);
                    continue;
                }
            }

            self.observer
                .on_backward_revisit(g, r, e, &deleted_set(g, r, &porf_e));
            if self.stopping() {
                return;
            }
            self.branch(first, &g2);
        }
    }

    /// `RevisitCondition(G, e', s)` (lines 17-22), where `porf_s` is the precomputed porf-prefix
    /// of the revisiting send `s` (passed as `revisiting`).
    ///
    /// Under `time_predicate` the nondet canon is the **existential PASS rule**
    /// (T2_ORACLE_SPEC §1.1): a `Deleted` nondet passes iff *no strictly smaller value is
    /// viable* — [`crate::time::viable`], an order-free DFS over completions of
    /// [`viability_base`]. PASS does not require the held value itself to be viable; debug
    /// builds report that separate diagnostic for nonminimum holders. A minimum holder
    /// passes with **zero** oracle calls. `&mut self` is used for the oracle memo.
    ///
    /// The blocking-receive canon (line 22) is now the **same existential rule** — see
    /// [`Self::pass_recv`]. It used to be the local `(avail,tid,idx)` tiebreaker, whose
    /// `earliest_times(trial)` filter tests *local* feasibility, a strict over-approximation of
    /// viability; that gap (risk R1) turned out to be a real, machine-confirmed completeness loss
    /// (`tests/r1_line22.rs`), not a theoretical one. Off the flag both arms use the untimed
    /// rules and the configured total consistent-source selector (EventId by default).
    fn revisit_condition(
        &mut self,
        g: &ExecutionGraph,
        ep: EventId,
        porf_s: &BTreeSet<EventId>,
        revisiting: EventId,
    ) -> bool {
        if !self.time_predicate && !self.canon_free {
            if self.source_order == SourceOrder::EventId {
                return super::ownership::untimed_revisit_condition(g, ep, porf_s);
            }
            return super::ownership::untimed_revisit_condition_with_order(
                g,
                ep,
                porf_s,
                self.source_order,
            );
        }
        match g.label(ep) {
            // line 18: a non-blocking receive is canonical iff it reads bottom. Under the
            // predicate that is the **existential PASS rule** too — see [`Self::pass_nb`]. The
            // old justification ("nb is time-transparent, so ⊥ is always feasible") confused
            // *local* feasibility with *viability* and cost a realizable terminal
            // (`tests/nb_line18.rs`); off the flag this is the exact untimed rule, unchanged.
            Label::Recv {
                blocking: false, ..
            } => {
                // L2′ / Т-RED′ (`T2_COMPLETENESS_VI_2` §0.1): arm 18 ≡ true. It must be forced
                // together with 19/22 — once `pass_nb` made this arm existential rather than
                // structural, an active arm 18 can reject a revisit zombie performs, and T2⁰
                // stops majorising the zombie tree. Т-RED as written over {19, 22} is refuted;
                // Т-RED′ over {18, 19, 22} is the proved form.
                if self.canon_free {
                    return true;
                }
                if g.reads_bottom(ep) {
                    return true; // ⊥ is the ≺-minimum: canonical under both rules, zero oracle calls
                }
                if !self.time_predicate {
                    return false;
                }
                let h = restrict_previous(g, ep, porf_s);
                self.pass_nb(g, ep, porf_s, revisiting, &h)
            }

            // line 22: a blocking receive is canonical iff it reads the tiebreaker send that the
            // oracle picks on G|_Previous (NOT on the full G). Untimed that is the `(tid, idx)`
            // minimum; under the predicate it is the **existential PASS rule** (R1 fix, below).
            Label::Recv { blocking: true, .. } => {
                // L2′ / Т-RED′'s T2⁰ (`T2_COMPLETENESS_VI_2` §0.1): arm 22 ≡ true. `true` is
                // weaker than *any* canon rule (untimed or PASS), so this can only add revisits —
                // the tree grows towards zombie's, never shrinks.
                if self.canon_free {
                    return true;
                }
                let h = restrict_previous(g, ep, porf_s);
                if !self.time_predicate {
                    return g.reads_from(ep) == get_cons_tiebreaker(&h, ep, false);
                }
                self.pass_recv(g, ep, porf_s, revisiting, &h)
            }

            // line 19: a nondet is canonical iff it chose its canonical value. Untimed: min(S).
            // Under the predicate: the existential PASS rule (T2_ORACLE_SPEC §1.1) —
            // PASS ⟺ ¬∃ v < v_held (resolved-string order): viable(v).
            Label::Nondet { set } => {
                // L2′ / Т-RED′'s T2⁰: arm 19 ≡ true (see the blocking-receive arm above).
                if self.canon_free {
                    return true;
                }
                if self.time_predicate {
                    let v_held = *g.nd_value(ep).expect("nondet has a value");
                    let held_str = crate::intern::resolve(v_held);
                    // The values strictly below the held one, in the canonical string order.
                    let mut smaller: Vec<Val> = set
                        .iter()
                        .copied()
                        .filter(|&v| crate::intern::resolve(v) < held_str)
                        .collect();
                    smaller
                        .sort_by(|a, b| crate::intern::resolve(*a).cmp(crate::intern::resolve(*b)));
                    if smaller.is_empty() {
                        // The minimum passes by the definition of PASS, without an oracle
                        // call. This does not assert that the held value is itself viable.
                        return true;
                    }
                    let base = viability_base(g, ep, porf_s);
                    let rev_label = g.label(revisiting).clone();
                    let refuted = smaller.into_iter().any(|v| {
                        let verdict = crate::time::viable(
                            &base,
                            ep,
                            v,
                            self.program,
                            &self.priorities,
                            revisiting,
                            &rev_label,
                            &mut self.viable_memo,
                        );
                        self.observer
                            .on_viable_verdict(&base, ep, v, revisiting, &rev_label, verdict);
                        verdict
                    });
                    self.report_self_viability(&base, ep, v_held, revisiting, &rev_label);
                    !refuted
                } else {
                    let min = set.iter().min_by(|a, b| {
                        crate::intern::resolve(**a).cmp(crate::intern::resolve(**b))
                    });
                    g.nd_value(ep) == min
                }
            }

            // line 21: any non-receive (send / error) is canonical iff no receive in Previous
            // reads it. Structural (no Fix-B change).
            Label::Send { .. } | Label::Error { .. } => {
                // "No receive of `Previous` reads `ep`" — asked directly of the receives
                // rather than by materialising `Previous` (`|E|` set inserts per deleted
                // send, and most deleted events are sends). `Previous` is
                // `{x | x <=G ep} ∪ porf(s)`, so membership is the stamp test below.
                let se = g.stamp(ep);
                !g.iter_recvs().any(|rp| {
                    g.reads_from(rp) == Some(ep) && (g.stamp(rp) <= se || porf_s.contains(&rp))
                })
            }
        }
    }

    /// Report held-value viability in debug builds without treating it as an invariant.
    ///
    /// Backward candidates are evaluated even when this send's forward gate failed. An
    /// individual arm can also run before another arm rejects the candidate. Consequently
    /// level 4 alone does not imply that the current holder is viable. Aborting here used
    /// to interrupt enumeration of valid terminals (the two-process regression in
    /// `tests/t2_diagnostics.rs`). A false answer remains observable for proof audits but
    /// does not change PASS or exploration. It also does not imply the whole viable set
    /// is empty, nor establish that a duplicate will be reported.
    ///
    /// As before, only nonminimum nondeterministic holders at level 4 are queried. The
    /// release implementation does no additional work.
    #[cfg(debug_assertions)]
    fn report_self_viability(
        &mut self,
        base: &ExecutionGraph,
        ep: EventId,
        v_held: Val,
        revisiting: EventId,
        rev_label: &Label,
    ) {
        if self.time_level < 4 {
            return;
        }
        let held_viable = crate::time::viable(
            base,
            ep,
            v_held,
            self.program,
            &self.priorities,
            revisiting,
            rev_label,
            &mut self.viable_memo,
        );
        self.observer
            .on_held_viable_verdict(base, ep, v_held, revisiting, rev_label, held_viable);
    }

    /// No-op outside debug builds — see the `cfg(debug_assertions)` twin.
    #[cfg(not(debug_assertions))]
    fn report_self_viability(
        &mut self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _v_held: Val,
        _revisiting: EventId,
        _rev_label: &Label,
    ) {
    }

    /// The **R1 fix**: line 22's blocking-receive canon as an *existential* rule, symmetric to
    /// the nondet arm's PASS (`C1_HARDENING_SPEC` §D.5, `R1_LINE22_SPEC`).
    ///
    /// ```text
    /// PASS_recv(ep) ⟺ ¬∃ s′ ≺ rf(ep) : viable_recv(s′)
    /// ```
    ///
    /// where `≺` is the unchanged `(avail_lb, tid, idx)` order over
    /// [`cons_candidates`]`(G|_Previous, ep)`.
    ///
    /// # Why the local tiebreaker was unsound (a *demonstrated* completeness loss)
    ///
    /// The old rule demanded `rf(ep) == min(candidates)`, where a candidate had merely to be
    /// *locally* eager-feasible (the `earliest_times(trial)` filter in [`cons_candidates`]).
    /// Local feasibility is a strict over-approximation of viability, so the canon could name a
    /// source **no completion can realize**: the branch holding it dies before reaching the
    /// revisit, the branch holding the genuinely viable source is refused as non-canonical, and
    /// the revisit fires from nowhere — a realizable terminal is lost. That is not theoretical:
    /// `tests/r1_line22.rs` pins the 4-thread witness (zombie/T1 = 3 realizable, old T2 = 2),
    /// where the canon named `s1@[10,10]` (`avail_lb` 10, locally feasible, **not** viable) over
    /// the held `s2@[20,20]` (viable). It is the structural twin of the historical raft f1
    /// 28-vs-40 loss, which the nondet arm's PASS rule already fixed.
    ///
    /// # Why this is completeness-safe by construction
    ///
    /// * **Old ⟹ new.** If the old arm passed, `rf(ep)` *was* the minimum, so no candidate is
    ///   `≺`-smaller and the new rule passes vacuously. The new arm therefore accepts at least
    ///   as often as the old one, and by M2-style monotonicity (`C1_HARDENING_SPEC` §0.1–0.2 —
    ///   the explorer's children are independent, so adding one never removes another) no
    ///   revisit that fires today can stop firing.
    /// * **Narrowing the viable set is the safe direction** (M1): candidates absent from
    ///   [`viability_base`] are answered "not viable" without a call — `rf` names an *event*, and
    ///   one inside `ep`'s dependency cone cannot be re-pinned at all. Fewer viable competitors
    ///   ⇒ PASS more often ⇒ at least as many revisits.
    /// * **Price**: duplicates (optimality-(a)), never loss — and discontinuously so: while some
    ///   `≺`-smaller candidate stays viable exactly one holder passes, but once *all* of them are
    ///   non-viable every reaching holder passes (`C1_HARDENING_SPEC` §0.7). The debug
    ///   held-value diagnostic records evidence relevant to that question without asserting
    ///   that an individual failed query implies a duplicate.
    /// * **Untimed projection**: off the flag this function is not called at all (the caller
    ///   short-circuits to the plain `(tid, idx)` minimum), so "flag OFF ⇒ byte-identical" holds
    ///   syntactically rather than by argument.
    ///
    /// The min-holder pays **zero** oracle calls (`pos == 0`), which is what keeps the rule free
    /// on value-independent programs, where it is behaviourally the old rule.
    fn pass_recv(
        &mut self,
        g: &ExecutionGraph,
        ep: EventId,
        porf_s: &BTreeSet<EventId>,
        revisiting: EventId,
        h: &ExecutionGraph,
    ) -> bool {
        let held = g.reads_from(ep);
        let cands = cons_candidates(h, ep, true);
        // The held source must itself be a candidate on `G|_Previous`. If it is not (its source
        // was cut by the restriction, or another receive of Previous consumed it), the old rule
        // was false too — `tiebreaker != held` — so this preserves the old verdict exactly.
        let Some(pos) = cands.iter().position(|&s| Some(s) == held) else {
            return false;
        };
        if pos == 0 {
            // Min-holder: canonical under the old rule, so canonical under the new one, with no
            // oracle call. This is the overwhelmingly common path.
            return true;
        }
        let base = viability_base(g, ep, porf_s);
        let rev_label = g.label(revisiting).clone();
        // Strictly `≺`-smaller candidates, in order: a single viable one refutes canonicity.
        let refuted = cands[..pos].iter().any(|&src| {
            // Not present in the base ⇒ not re-pinnable ⇒ answered "not viable" (M1-safe).
            if base.thread_len(src.tid) <= src.idx {
                return false;
            }
            let verdict = crate::time::viable_recv(
                &base,
                ep,
                src,
                self.program,
                &self.priorities,
                revisiting,
                &rev_label,
                &mut self.viable_memo,
            );
            self.observer
                .on_viable_recv_verdict(&base, ep, src, revisiting, &rev_label, verdict);
            verdict
        });
        !refuted
    }

    /// The **line-18 fix**: the non-blocking-receive canon as an *existential* rule, symmetric to
    /// [`Self::pass_recv`] and to the nondet arm's PASS (`T2_GAMMA_FRONTIER` §Ⅱ recipe R-1).
    ///
    /// ```text
    /// PASS_nb(ep) ⟺ reads_bottom(ep)                                    // handled by the caller
    ///             ∨ ( ¬viable_recv_bot(base, ep)                        // ⊥ is the ≺-minimum
    ///               ∧ ¬∃ σ′ ≺ rf(ep) ∈ cons_candidates(G|_Previous, ep) : viable_recv(base, ep, σ′) )
    /// ```
    ///
    /// The option order of a non-blocking receive is `⊥ ≺ cons_candidates(…)`: ⊥ *is* the untimed
    /// canon, so it is the minimum, and the sends below the held one are ranked by the unchanged
    /// `(avail_lb, tid, idx)` key.
    ///
    /// # Why the ⊥ canon was unsound (a *demonstrated* completeness loss)
    ///
    /// The old rule accepted only `rf(ep) = ⊥`, on the grounds that a non-blocking receive is
    /// time-transparent and so ⊥ is always *locally* feasible. Local feasibility is a strict
    /// over-approximation of viability: reading ⊥ leaves the message **unconsumed**, and an
    /// unconsumed message is a competitor in the B-clause of every later matching blocking
    /// receive — and, when the body is value-dependent, the ⊥ branch may emit an early-window
    /// send that kills the region outright. The canonical branch then never emits the revisiting
    /// send, the branch that does emit it is refused as non-canonical, and the revisit fires from
    /// nowhere. `tests/nb_line18.rs` pins the 4-thread witness (zombie/T1 = 3 realizable, old
    /// T2 = 2, lost terminal `r←L, ep←s, q←m`) and its 7-vs-4 nondet composite. It is the third
    /// instance of one defect, after the nondet arm (raft f1 28-vs-40) and line 22
    /// (`tests/r1_line22.rs`).
    ///
    /// # Why this is completeness-safe by construction
    ///
    /// * **Old ⟹ new.** The old arm passed only on `reads_bottom(ep)`, which the caller answers
    ///   `true` before reaching here. The new arm therefore accepts a strict superset, and by
    ///   M2-style monotonicity (`C1_HARDENING_SPEC` §0.1–0.2) no revisit that fires today can
    ///   stop firing.
    /// * **At most one holder passes** (optimality-(a)): PASS is antitone in the viable set, and
    ///   a ⊥-holder that reaches the revisit is its own witness that ⊥ is viable — which is
    ///   exactly what refuses every non-⊥ holder. Only when ⊥ is *unreachable* does a non-⊥
    ///   holder take over.
    /// * **Narrowing the viable set is the safe direction** (M1): a candidate absent from
    ///   [`viability_base`] is answered "not viable" without a call.
    /// * **Untimed projection**: off the flag the caller short-circuits to `reads_bottom(ep)`, so
    ///   "flag OFF ⇒ byte-identical" holds syntactically.
    ///
    /// # Price
    ///
    /// Unlike [`Self::pass_recv`], there is no free min-holder path here: **every** non-⊥
    /// non-blocking receive in `Deleted` now costs one `viable_recv_bot` call, where before it
    /// was rejected for free. Programs with many non-blocking receives (raft's monitor
    /// `recv_timeout`s) pay it on every revisit attempt; the memo absorbs most of it, and the
    /// measured cost is recorded in the report accompanying this change.
    fn pass_nb(
        &mut self,
        g: &ExecutionGraph,
        ep: EventId,
        porf_s: &BTreeSet<EventId>,
        revisiting: EventId,
        h: &ExecutionGraph,
    ) -> bool {
        let held = g.reads_from(ep);
        debug_assert!(held.is_some(), "pass_nb is only called on a non-⊥ read");
        let cands = cons_candidates(h, ep, true);
        // The held source must itself be a candidate on `G|_Previous` (it is not when a stamp
        // inversion put it outside `Previous`, or another receive of `Previous` consumed it). Then
        // the ≺-smaller set is not computable here, and the old verdict — `false` — is kept.
        let Some(pos) = cands.iter().position(|&s| Some(s) == held) else {
            return false;
        };
        let base = viability_base(g, ep, porf_s);
        let rev_label = g.label(revisiting).clone();
        // ⊥ first: it is the ≺-minimum, so a viable ⊥ refutes every non-⊥ holder on its own.
        if crate::time::viable_recv_bot(
            &base,
            ep,
            self.program,
            &self.priorities,
            revisiting,
            &rev_label,
            &mut self.viable_memo,
        ) {
            return false;
        }
        // Then the strictly `≺`-smaller sends, exactly as `pass_recv` does.
        let refuted = cands[..pos].iter().any(|&src| {
            // Not present in the base ⇒ not re-pinnable ⇒ answered "not viable" (M1-safe).
            if base.thread_len(src.tid) <= src.idx {
                return false;
            }
            let verdict = crate::time::viable_recv(
                &base,
                ep,
                src,
                self.program,
                &self.priorities,
                revisiting,
                &rev_label,
                &mut self.viable_memo,
            );
            self.observer
                .on_viable_recv_verdict(&base, ep, src, revisiting, &rev_label, verdict);
            verdict
        });
        !refuted
    }
}

/// The base graph the existential oracle [`crate::time::viable`] searches from
/// (T2_ORACLE_SPEC §1.2): **`G|_Previous` minus the dependency cone of `ep`**.
///
/// Why not the bare stamp prefix (the v1 Fix-B `restrict_below`): that would drop — and force `viable` to
/// re-derive — the part of porf-prefix(`s`) with stamps above `stamp(ep)`, which is exactly the
/// content of `G_rs` the revisit *preserves verbatim* (`Deleted` = stamps > r ∧ ∉ prefix(s),
/// §4.3 line 11); re-deriving preserved content is an independent channel of spurious verdict
/// divergence (including a spurious failure of the `contains(revisiting)` success test). Why not
/// all of `Previous`: events whose values (transitively) depend on `ep`'s held value carry stale
/// labels once `viable` re-pins `ep` to a *different* `v` (the Д1 bug, raft f0 8→4). The right
/// base keeps `Previous` and drops only that dependency cone.
///
/// The cone is a fixpoint over `g`'s `(E, po, rf)` (never stamps): `diverge_idx[t]` is the first
/// po-index of thread `t` known to depend on `ep`'s value, seeded with `diverge_idx[tid(ep)] =
/// idx(ep) + 1` (`ep` itself stays — `viable` re-pins its value). A receive `r′ ∈ Previous`
/// whose source lies in the cone is dropped **inclusively** (its label does not depend on what
/// it read, but its rf and value do — over-approximating dependency is the sound direction,
/// O6), and everything po-after it on its thread goes with it.
///
/// The keep set is valid for [`ExecutionGraph::restrict`]: the cone is po-suffix per thread
/// (an index threshold), so its complement inside the po-prefix-closed `Previous` is
/// po-prefix-closed; and any receive reading a cone send is itself in the cone, so the cut
/// leaves no dangling rf into the cone.
pub(crate) fn viability_base(
    g: &ExecutionGraph,
    ep: EventId,
    porf_s: &BTreeSet<EventId>,
) -> ExecutionGraph {
    let previous = previous_set(g, ep, porf_s);
    let n = g.num_threads();
    // diverge_idx[t] = first po-index of thread t inside the cone (usize::MAX = none).
    let mut diverge = vec![usize::MAX; n];
    diverge[ep.tid] = ep.idx + 1;
    loop {
        let mut changed = false;
        for &rp in &previous {
            if !g.label(rp).is_recv() {
                continue;
            }
            let Some(sp) = g.reads_from(rp) else {
                continue;
            };
            if sp.idx >= diverge[sp.tid] && rp.idx < diverge[rp.tid] {
                // Source in the cone ⇒ the reader joins it, inclusively.
                diverge[rp.tid] = rp.idx;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let keep: BTreeSet<EventId> = previous
        .into_iter()
        .filter(|e| e.idx < diverge[e.tid])
        .collect();
    g.restrict(&keep)
}

/// `Deleted = { e' in G.E | r <G e' and (e', s) not in G.porf }` (line 11), with `porf_s`
/// the precomputed porf-prefix of `s`. Strict `<G`; `s`'s porf-prefix is preserved. `s`
/// itself is included (it is <=G-maximal and not in its own porf-prefix), but the caller
/// keeps it in the graph.
fn deleted_set(g: &ExecutionGraph, r: EventId, porf_s: &BTreeSet<EventId>) -> BTreeSet<EventId> {
    let sr = g.stamp(r);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) > sr && !porf_s.contains(&x))
        .collect()
}

/// `Previous = { e' in G.E | e' <=G e or (e', s) in G.porf }` (line 20), with `porf_s` the
/// precomputed porf-prefix of the revisiting send `s`. Non-strict `<=G` (so `e` itself is
/// in Previous), and the porf part is strict up to `s`. This encodes "as of when e was
/// added": from the future, e sees only s's porf-prefix, which is guaranteed to remain.
/// The set is po-prefix-closed (stamp-downward within each thread plus a porf-prefix), so
/// `restrict` accepts it as a keep set.
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
///
/// # T-CANON: time-aware canonical source (T2_PLAN §2d, Lemma 2)
///
/// Under `time_predicate` the canonical read is the **earliest guaranteed arrival**, so a
/// candidate is additionally required to be eager-time-*feasible* for `e` to read (aligning with
/// T-PRED, which only ever lets `e` read a feasible source), and the survivors are ranked by
/// `(avail_lb(s), tid, idx)` instead of `(tid, idx)` — earliest `avail`-LB first, ties by
/// `(tid, idx)`. `avail_lb(s)` is a property of `s`'s own channel prefix (independent of who
/// reads it), so it is read off `earliest_times(trial)` where `trial = hp` with `e ← s`; that
/// `trial` is consistent (guards passed) and hence has no ⊥-reading blocking receive, so the
/// time system is well formed. The guards (steps 1–2, i.e. "a revisiting send stays a candidate"
/// and "no other receive reads it", line 21) run **before** the tiebreaker, unchanged.
///
/// With `time_predicate` off, every `avail` is `None`, so the ranking collapses to the exact
/// `(tid, idx)`-minimal of the untimed algorithm — byte-identical behaviour.
pub fn get_cons_tiebreaker(
    h: &ExecutionGraph,
    e: EventId,
    time_predicate: bool,
) -> Option<EventId> {
    if time_predicate {
        // The `(avail_lb, tid, idx)` key can rank a later send first, so every candidate has
        // to be built and scored.
        return cons_candidates(h, e, time_predicate).first().copied();
    }
    // Untimed the key is `(tid, idx)` and `iter_sends` already walks that order, so the
    // first candidate that passes the guards *is* the minimum: stop there instead of
    // scoring every remaining send (this runs for every blocking receive in `Deleted`, of
    // every candidate revisit). The trial read is applied in place and rolled back, which
    // also drops the graph clone each candidate used to cost.
    let mut hp = h.clone();
    hp.set_rf(e, None); // guard 1: remove e's own rf edge
    let candidates: Vec<EventId> = hp
        .iter_sends()
        .filter(|&s| {
            // guard 2 (line 21): matches, and unread by any receive other than e.
            hp.matches(s, e)
                && !hp
                    .iter_recvs()
                    .any(|rp| rp != e && hp.reads_from(rp) == Some(s))
        })
        .collect();
    let mut found = None;
    for s in candidates {
        hp.set_rf(e, Some(s));
        if consistent(&hp) {
            found = Some(s);
            break;
        }
    }
    hp.set_rf(e, None);
    found
}

/// A total untimed-consistent source selector under the configured stable order.
///
/// Unlike the T2 candidate path, this never rejects a source for temporal infeasibility.
/// The old held RF is erased, all matching unread sources remain eligible, and full
/// untimed consistency decides admissibility. The public original-order API above is
/// unchanged, including its early-exit fast path.
pub(crate) fn get_cons_tiebreaker_with_order(
    h: &ExecutionGraph,
    e: EventId,
    order: SourceOrder,
) -> Option<EventId> {
    if order == SourceOrder::EventId {
        return get_cons_tiebreaker(h, e, false);
    }
    let mut trial = h.clone();
    trial.set_rf(e, None);
    let mut candidates: Vec<_> = trial
        .iter_sends()
        .filter(|&s| {
            trial.matches(s, e)
                && !trial
                    .iter_recvs()
                    .any(|r| r != e && trial.reads_from(r) == Some(s))
        })
        .collect();
    candidates.sort_by_key(|&s| order.key(&trial, s));
    for source in candidates {
        trial.set_rf(e, Some(source));
        if consistent(&trial) {
            return Some(source);
        }
    }
    None
}

/// Every send `e` could canonically read on `h`, in the tiebreaker order — `(avail_lb, tid, idx)`
/// under `time_predicate`, plain `(tid, idx)` off it. [`get_cons_tiebreaker`] is its head; the
/// R1 rule (§D.5, [`super::Explorer::revisit_condition`]) needs the whole ordered list, because
/// "is the held source canonical?" becomes "is any *strictly earlier* candidate viable?".
///
/// Guards, filter and ordering are exactly those documented on [`get_cons_tiebreaker`] — this is
/// that function with the final `min_by` replaced by a `sort_by`, so the two can never drift.
pub(crate) fn cons_candidates(
    h: &ExecutionGraph,
    e: EventId,
    time_predicate: bool,
) -> Vec<EventId> {
    let mut hp = h.clone();
    hp.set_rf(e, None); // guard 1: remove e's own rf edge

    // Candidate `(send, avail_lb)`; `avail_lb` is `None` off the predicate (pure (tid,idx) order).
    let mut cands: Vec<(EventId, Option<i64>)> = Vec::new();
    for s in hp.iter_sends().collect::<Vec<_>>() {
        if !hp.matches(s, e) {
            continue;
        }
        // guard 2 (line 21): unread by any receive other than e.
        let read_by_other = hp
            .iter_recvs()
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
        let avail = if time_predicate {
            // Feasibility filter + earliest-arrival key. An eager-infeasible read is never a
            // canonical source (T-PRED would have pruned it), so skip it entirely.
            match crate::time::earliest_times(&trial) {
                Some(earliest) => earliest.avail_lb(s), // Some for a send present in `trial`
                None => continue,
            }
        } else {
            None
        };
        cands.push((s, avail));
    }
    // Sort by `(avail_lb, (tid, idx))`. `Option<i64>` orders `None < Some`, but under the
    // predicate every kept candidate has `Some(avail)`, and off it every candidate has `None`,
    // so this is exactly `(avail_lb, tid, idx)` on and `(tid, idx)` off.
    cands.sort_by(|(sa, aa), (sb, ab)| (aa, sa).cmp(&(ab, sb)));
    cands.into_iter().map(|(s, _)| s).collect()
}

#[cfg(test)]
mod source_order_tests {
    use super::*;
    use crate::event::{Model, Pred, Window};

    #[test]
    fn self_send_order_is_rf_blind_and_does_not_filter_late_sources() {
        let mut g = ExecutionGraph::new();
        let remote = g.add_event(
            0,
            Label::send_within(Model::Asyn, 1, "remote", Window::new(1, 1)),
        );
        let local = g.add_event(
            1,
            Label::send_within(Model::Asyn, 1, "local", Window::new(10, 10)),
        );
        let r = g.add_event(1, Label::recv(Pred::any()));
        for held in [remote, local] {
            g.set_rf(r, Some(held));
            assert_eq!(get_cons_tiebreaker(&g, r, false), Some(remote));
            assert_eq!(
                get_cons_tiebreaker_with_order(&g, r, SourceOrder::SelfSendFirst),
                Some(local)
            );
        }
        assert!(!crate::time::check(&g).is_feasible());
    }

    #[test]
    fn preferred_source_still_requires_full_untimed_consistency() {
        for model in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
            let mut g = ExecutionGraph::new();
            let remote = g.add_event(0, Label::send(model, 1, "remote"));
            let r = g.add_event(1, Label::recv(Pred::any()));
            g.set_rf(r, Some(remote));
            let cyclic = g.add_event(1, Label::send(model, 1, "too-late"));
            assert!(
                SourceOrder::SelfSendFirst.key(&g, cyclic)
                    < SourceOrder::SelfSendFirst.key(&g, remote)
            );
            assert_eq!(
                get_cons_tiebreaker_with_order(&g, r, SourceOrder::SelfSendFirst),
                Some(remote)
            );
        }
    }

    #[test]
    fn preferred_source_consumed_by_another_receive_is_excluded() {
        let mut g = ExecutionGraph::new();
        let remote = g.add_event(0, Label::send(Model::Asyn, 1, "remote"));
        let local = g.add_event(1, Label::send(Model::Asyn, 1, "local"));
        let first = g.add_event(1, Label::recv(Pred::eq("local")));
        g.set_rf(first, Some(local));
        let next = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(next, Some(remote));
        assert_eq!(
            get_cons_tiebreaker_with_order(&g, next, SourceOrder::SelfSendFirst),
            Some(remote)
        );
    }
}

#[cfg(test)]
mod viability_base_tests {
    //! O6 units (T2_ORACLE_SPEC §1.8): the dependency cone is a sound over-approximation —
    //! po-suffix per thread, propagated along rf, readers dropped inclusively — and everything
    //! independent of `ep` survives with its rf intact.

    use super::*;
    use crate::event::{Model, Pred};

    fn nd(set: &[&str]) -> Label {
        Label::nondet(set.iter().copied())
    }
    fn send(dst: usize, v: &str) -> Label {
        Label::send(Model::Asyn, dst, v)
    }
    fn recv() -> Label {
        Label::recv(Pred::any())
    }

    /// rf-propagation + inclusiveness: the cone starts po-after `ep`, swallows the reader of a
    /// cone send (the reader itself, not just its suffix), and cascades one more rf hop.
    #[test]
    fn cone_propagates_along_rf_inclusively() {
        let mut g = ExecutionGraph::new();
        let ep = g.add_event(0, nd(&["a", "b"]));
        g.set_nd(ep, "a".into());
        let s01 = g.add_event(0, send(1, "x"));
        let r10 = g.add_event(1, recv());
        g.set_rf(r10, Some(s01));
        let s11 = g.add_event(1, send(2, "y"));
        let r20 = g.add_event(2, recv());
        g.set_rf(r20, Some(s11));

        // Previous = everything (delivered via porf_s; stamps above ep's are not ≤_G ep).
        let porf_s: BTreeSet<EventId> = vec![s01, r10, s11, r20].into_iter().collect();
        let base = viability_base(&g, ep, &porf_s);

        // ep survives (its value is re-pinned by the oracle); its po-suffix (s01) is cone;
        // r10 read s01 ⇒ dropped inclusively, s11 goes as its po-suffix; r20 read s11 ⇒ dropped.
        assert_eq!(base.thread_len(0), 1, "only ep survives on thread 0");
        assert_eq!(
            base.thread_len(1),
            0,
            "reader of a cone send is dropped inclusively"
        );
        assert_eq!(base.thread_len(2), 0, "second rf hop is dropped too");
        assert_eq!(
            base.nd_value(ep),
            Some(&"a".into()),
            "ep keeps its (re-pinnable) value"
        );
    }

    /// Events independent of `ep` survive with their rf intact.
    #[test]
    fn independent_events_survive() {
        let mut g = ExecutionGraph::new();
        let ep = g.add_event(0, nd(&["a", "b"]));
        g.set_nd(ep, "b".into());
        let s10 = g.add_event(1, send(2, "x"));
        let r20 = g.add_event(2, recv());
        g.set_rf(r20, Some(s10));

        let porf_s: BTreeSet<EventId> = vec![s10, r20].into_iter().collect();
        let base = viability_base(&g, ep, &porf_s);

        assert_eq!(base.thread_len(0), 1);
        assert_eq!(base.thread_len(1), 1);
        assert_eq!(base.thread_len(2), 1);
        assert_eq!(
            base.reads_from(r20),
            Some(s10),
            "independent rf is preserved"
        );
    }

    /// The base is `G|_Previous` minus the cone — an event outside Previous is dropped even
    /// when independent of `ep`.
    #[test]
    fn outside_previous_is_dropped() {
        let mut g = ExecutionGraph::new();
        let ep = g.add_event(0, nd(&["a", "b"]));
        g.set_nd(ep, "a".into());
        let s10 = g.add_event(1, send(2, "x"));
        let _s11 = g.add_event(1, send(2, "z")); // NOT in Previous
        let r20 = g.add_event(2, recv());
        g.set_rf(r20, Some(s10));

        let porf_s: BTreeSet<EventId> = vec![s10, r20].into_iter().collect();
        let base = viability_base(&g, ep, &porf_s);

        assert_eq!(
            base.thread_len(1),
            1,
            "s11 ∉ Previous is cut (po-prefix keeps s10)"
        );
        assert_eq!(base.reads_from(r20), Some(s10));
    }

    /// The fixpoint iterates: a reader on a smaller tid depends on a cone discovered later in
    /// the (tid, idx) scan, so one pass is not enough.
    #[test]
    fn fixpoint_needs_second_round() {
        let mut g = ExecutionGraph::new();
        let ep = g.add_event(0, nd(&["a", "b"]));
        g.set_nd(ep, "a".into());
        let s01 = g.add_event(0, send(2, "x"));
        let r20 = g.add_event(2, recv());
        g.set_rf(r20, Some(s01));
        let s21 = g.add_event(2, send(1, "y"));
        let r10 = g.add_event(1, recv());
        g.set_rf(r10, Some(s21));

        let porf_s: BTreeSet<EventId> = vec![s01, r20, s21, r10].into_iter().collect();
        let base = viability_base(&g, ep, &porf_s);

        // (2,0) reads the cone send (0,1) ⇒ thread 2 cone from idx 0; (1,0) reads (2,1) which
        // is now cone ⇒ thread 1 cone from idx 0 — discovered only on the second round.
        assert_eq!(base.thread_len(0), 1);
        assert_eq!(base.thread_len(1), 0);
        assert_eq!(base.thread_len(2), 0);
    }
}
