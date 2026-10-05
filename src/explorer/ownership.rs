//! Bounded certificates for pruning an entire original-MUST construction subtree.
//!
//! A temporal conflict proves that a graph has no valid *forward* completion. It does
//! not by itself justify discarding the sends that would construct backward revisits.
//! This module supplies one deliberately conservative bridge: inspect the ordinary
//! forward skeleton, preserving construction stamps, and certify that **every**
//! backward revisit encountered there is rejected by the untimed canonical rule.
//!
//! If that skeleton is exhausted and every forward terminal is time-infeasible, its
//! entire MUST subtree is barren. Any admitted revisit leaves an outstanding obligation
//! and returns `Unknown`; we neither guess another owner nor change canonicity.
//! A budget limit also returns `Unknown`. The bounded inspection is real work, reported
//! separately in [`OwnershipStats`]; it does not make that work disappear from complexity.
//!
//! Certificates apply only to original MUST's canonical construction under the specified
//! priority/DES and source-order policies, with no T2 gates, receive predicates, or
//! relaxed canonical arms. The public entry point uses the original EventId source order;
//! the parent explorer passes its configured total consistent-source selector internally.
//! No stamp-free graph-key memoization is used.

use std::collections::BTreeSet;
use std::sync::Arc;

use super::source_order::SourceOrder;
use crate::consistency::consistent;
use crate::event::{EventId, Label, Model, Tid};
use crate::graph::ExecutionGraph;
use crate::program::Program;
use crate::scheduler::{pick, traces_of, NextStep};

use super::revisit::{get_cons_tiebreaker_with_order, restrict_previous};

/// Maximum forward states inspected and total temporary event append operations.
/// Reaching either limit leaves the construction obligation unresolved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OwnershipBudget {
    pub max_states: usize,
    pub max_added_events: usize,
}

impl Default for OwnershipBudget {
    fn default() -> Self {
        Self {
            max_states: 128,
            max_added_events: 64,
        }
    }
}

/// Work performed by a single certificate query, including unsuccessful queries.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OwnershipStats {
    pub states: usize,
    pub added_events: usize,
    pub revisit_candidates: usize,
    pub canonical_checks: usize,
    pub forward_terminals: usize,
}

/// An actual original-MUST backward construction which has not been discharged.
/// Its target need not be time-feasible: this layer does not speculate about the
/// target's later revisits or assign its ownership to another construction.
#[derive(Clone, Debug)]
pub struct RevisitObligation {
    pub source: ExecutionGraph,
    pub target: ExecutionGraph,
    pub receive: EventId,
    pub send: EventId,
}

#[derive(Clone, Debug)]
pub enum OwnershipUnknown {
    StateBudgetExhausted,
    EventBudgetExhausted,
    /// Conservatively leave errors to the configured main explorer.
    ErrorEvent {
        event: EventId,
    },
    /// Do not invoke Asyn/P2p timing semantics for a speculative Cd/Mbox graph.
    UnsupportedModel {
        event: EventId,
    },
    InconsistentInput,
    InvalidPriorities,
    /// A real admitted revisit, including its construction graph and target.
    OutstandingRevisit(RevisitObligation),
}

/// Evidence that the inspected construction has no feasible forward terminal and
/// no admitted backward revisit anywhere in its forward skeleton.
///
/// Fields are private so this evidence can only be produced by the exhaustive check.
/// This is a per-query certificate, not a reusable cross-program cache entry.
#[derive(Clone, Debug)]
pub struct PruneCertificate {
    root: ExecutionGraph,
    priorities: Vec<Tid>,
    des: bool,
    source_order: SourceOrder,
    stats: OwnershipStats,
}

impl PruneCertificate {
    pub fn stats(&self) -> &OwnershipStats {
        &self.stats
    }

    /// Check the graph and policy scope of this certificate, including every existing
    /// construction stamp and receive-predicate object. Predicate text alone does not
    /// identify its semantics. The caller must additionally retain the same `Program`
    /// semantics used by the fresh query. This public entry point requires the original
    /// EventId source order; internal configured-order calls use `applies_to_with_order`.
    ///
    /// The graph's private next-stamp counter need not be identical: every future
    /// stamp is greater than every existing stamp, and only their order is observed.
    pub fn applies_to(&self, g: &ExecutionGraph, priorities: &[Tid], des: bool) -> bool {
        self.applies_to_with_order(g, priorities, des, SourceOrder::EventId)
    }

    /// The same construction check, additionally binding the chosen source order.
    pub(crate) fn applies_to_with_order(
        &self,
        g: &ExecutionGraph,
        priorities: &[Tid],
        des: bool,
        source_order: SourceOrder,
    ) -> bool {
        self.source_order == source_order
            && self.des == des
            && self.priorities == priorities
            && self.root.num_threads() == g.num_threads()
            && (0..g.num_threads()).all(|tid| self.root.thread_len(tid) == g.thread_len(tid))
            && self.root.iter_events().all(|event| {
                self.root.stamp(event) == g.stamp(event)
                    && self.root.label(event) == g.label(event)
                    && match (self.root.label(event), g.label(event)) {
                        (Label::Recv { pred: a, .. }, Label::Recv { pred: b, .. }) => {
                            Arc::ptr_eq(a, b)
                        }
                        _ => true,
                    }
                    && self.root.reads_from(event) == g.reads_from(event)
                    && self.root.nd_value(event) == g.nd_value(event)
            })
    }
}

#[derive(Clone, Debug)]
pub enum OwnershipCheck {
    Certified(PruneCertificate),
    Unknown {
        reason: OwnershipUnknown,
        stats: OwnershipStats,
    },
    /// A genuine time-feasible forward terminal refutes barrenness of this subtree.
    FeasibleTerminal {
        graph: ExecutionGraph,
        stats: OwnershipStats,
    },
}

impl OwnershipCheck {
    pub fn stats(&self) -> &OwnershipStats {
        match self {
            Self::Certified(certificate) => certificate.stats(),
            Self::Unknown { stats, .. } | Self::FeasibleTerminal { stats, .. } => stats,
        }
    }
}

/// Original Algorithm 1, lines 18/19/21/22, shared with the untimed main explorer.
/// `porf_s` is the causal prefix of the newly emitted revisiting send. In particular,
/// the blocking-receive tiebreaker is evaluated on `Previous`, not the full graph.
pub(crate) fn untimed_revisit_condition(
    g: &ExecutionGraph,
    ep: EventId,
    porf_s: &BTreeSet<EventId>,
) -> bool {
    untimed_revisit_condition_with_order(g, ep, porf_s, SourceOrder::EventId)
}

/// Original canonical arms with a total, untimed-consistent source-order policy.
pub(crate) fn untimed_revisit_condition_with_order(
    g: &ExecutionGraph,
    ep: EventId,
    porf_s: &BTreeSet<EventId>,
    source_order: SourceOrder,
) -> bool {
    match g.label(ep) {
        Label::Recv {
            blocking: false, ..
        } => g.reads_bottom(ep),
        Label::Recv { blocking: true, .. } => {
            let h = restrict_previous(g, ep, porf_s);
            g.reads_from(ep) == get_cons_tiebreaker_with_order(&h, ep, source_order)
        }
        Label::Nondet { set } => {
            let min = set
                .iter()
                .min_by(|a, b| crate::intern::resolve(**a).cmp(crate::intern::resolve(**b)));
            g.nd_value(ep) == min
        }
        Label::Send { .. } | Label::Error { .. } => {
            let stamp = g.stamp(ep);
            !g.iter_recvs().any(|r| {
                g.reads_from(r) == Some(ep) && (g.stamp(r) <= stamp || porf_s.contains(&r))
            })
        }
    }
}

/// Exact original candidate, target-consistency, and canonical tests. A `None`
/// answer proves that this newly emitted send has no backward construction children.
fn first_untimed_revisit(
    g: &ExecutionGraph,
    send: EventId,
    stats: &mut OwnershipStats,
    source_order: SourceOrder,
) -> Option<RevisitObligation> {
    let porf_send = g.porf_prefix(send);
    for receive in g.iter_recvs() {
        if !g.matches(send, receive) || porf_send.contains(&receive) {
            continue;
        }
        stats.revisit_candidates += 1;
        let stamp = g.stamp(receive);
        let keep = g
            .iter_events()
            .filter(|&x| g.stamp(x) <= stamp || porf_send.contains(&x) || x == send)
            .collect();
        let mut target = g.restrict(&keep);
        target.set_rf(receive, Some(send));
        if !consistent(&target) {
            continue;
        }
        let accepted = g
            .iter_events()
            .filter(|&x| g.stamp(x) > stamp && !porf_send.contains(&x))
            .chain(std::iter::once(receive))
            .all(|ep| {
                stats.canonical_checks += 1;
                untimed_revisit_condition_with_order(g, ep, &porf_send, source_order)
            });
        if accepted {
            return Some(RevisitObligation {
                source: g.clone(),
                target,
                receive,
                send,
            });
        }
    }
    None
}

/// Attempt to certify a barren original-MUST subtree.
///
/// The walk uses the same `pick`, receive consistency, and nondeterministic choices
/// as the main untimed explorer. It inspects each newly emitted send before following
/// its forward child. If a revisit is admitted, inspection stops with an obligation.
/// Otherwise this forward skeleton is the whole construction subtree. Consequently,
/// exhausting it with only infeasible terminals proves safe pruning by induction on
/// the finite inspected tree. No semantic-completion certificate is blindly trusted:
/// terminal feasibility is checked here independently as a final safeguard.
///
/// Existing sends are not reprocessed. Their backward-revisit loops belong to ancestor
/// send calls, outside the `Visit(g)` subtree this certificate describes; pruning a
/// forward child must leave those ancestor loops intact.
/// A zero event budget can still inspect a terminal (it appends no event); a zero
/// state budget cannot inspect even the root and always returns `Unknown`.
pub fn certify_no_escape<P: Program>(
    program: &P,
    g: &ExecutionGraph,
    priorities: &[Tid],
    des: bool,
    budget: OwnershipBudget,
) -> OwnershipCheck {
    certify_no_escape_with_order(program, g, priorities, des, budget, SourceOrder::EventId)
}

/// Inspect the same construction tree as the main explorer's configured source order.
pub(crate) fn certify_no_escape_with_order<P: Program>(
    program: &P,
    g: &ExecutionGraph,
    priorities: &[Tid],
    des: bool,
    budget: OwnershipBudget,
    source_order: SourceOrder,
) -> OwnershipCheck {
    let mut stats = OwnershipStats::default();
    let unknown = |reason, stats| OwnershipCheck::Unknown { reason, stats };
    let n = program.num_threads();
    let mut seen = vec![false; n];
    if priorities.len() != n
        || priorities.iter().any(|&tid| {
            if tid >= n || seen[tid] {
                return true;
            }
            seen[tid] = true;
            false
        })
    {
        return unknown(OwnershipUnknown::InvalidPriorities, stats);
    }
    if g.num_threads() > n || !consistent(g) {
        return unknown(OwnershipUnknown::InconsistentInput, stats);
    }
    if let Some(event) = g
        .iter_sends()
        .find(|&event| matches!(g.send_model(event), Some(Model::Cd | Model::Mbox)))
    {
        return unknown(OwnershipUnknown::UnsupportedModel { event }, stats);
    }

    // An explicit stack bounds Rust call-stack use. No graph interning or memoization:
    // equal terminal keys can carry different construction histories/stamps.
    let mut pending = vec![g.clone()];
    while let Some(current) = pending.pop() {
        if stats.states >= budget.max_states {
            return unknown(OwnershipUnknown::StateBudgetExhausted, stats);
        }
        stats.states += 1;
        let traces = traces_of(&current, n);
        let nexts = program.next(&traces);
        let (tid, label) = match pick(&current, &nexts, priorities, des) {
            NextStep::Terminal { .. } => {
                stats.forward_terminals += 1;
                if crate::time::eager_feasible(&current) {
                    return OwnershipCheck::FeasibleTerminal {
                        graph: current,
                        stats,
                    };
                }
                continue;
            }
            NextStep::Event { tid, label } => (tid, label),
        };
        if stats.added_events >= budget.max_added_events {
            return unknown(OwnershipUnknown::EventBudgetExhausted, stats);
        }
        let mut child = current.clone();
        stats.added_events += 1;
        let event = child.add_event(tid, label.clone());
        let mut children = Vec::new();
        match label {
            Label::Error { .. } => {
                return unknown(OwnershipUnknown::ErrorEvent { event }, stats);
            }
            Label::Send {
                model: Model::Cd | Model::Mbox,
                ..
            } => {
                return unknown(OwnershipUnknown::UnsupportedModel { event }, stats);
            }
            Label::Send { .. } => {
                if let Some(obligation) =
                    first_untimed_revisit(&child, event, &mut stats, source_order)
                {
                    return unknown(OwnershipUnknown::OutstandingRevisit(obligation), stats);
                }
                // Same maximal-unread-send consistency invariant as visit_send.
                debug_assert!(consistent(&child));
                children.push(child);
            }
            Label::Nondet { set } => {
                for &value in set.iter() {
                    child.set_nd(event, value);
                    children.push(child.clone());
                    if children.len()
                        > budget
                            .max_states
                            .saturating_sub(stats.states + pending.len())
                    {
                        return unknown(OwnershipUnknown::StateBudgetExhausted, stats);
                    }
                }
            }
            Label::Recv { .. } => {
                let sources: Vec<_> = child
                    .iter_sends()
                    .map(Some)
                    .chain(std::iter::once(None))
                    .collect();
                for source in sources {
                    child.set_rf(event, source);
                    if consistent(&child) {
                        children.push(child.clone());
                        if children.len()
                            > budget
                                .max_states
                                .saturating_sub(stats.states + pending.len())
                        {
                            return unknown(OwnershipUnknown::StateBudgetExhausted, stats);
                        }
                    }
                }
            }
        }
        // Reverse the stack push to preserve the main explorer's sibling order.
        pending.extend(children.into_iter().rev());
    }
    OwnershipCheck::Certified(PruneCertificate {
        root: g.clone(),
        priorities: priorities.to_vec(),
        des,
        source_order,
        stats,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::{Model, Pred, Val, Window};
    use crate::program::ThreadNext;

    struct Seq(Vec<Vec<Label>>);
    impl Program for Seq {
        fn num_threads(&self) -> usize {
            self.0.len()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.0
                .iter()
                .zip(traces)
                .map(|(body, trace)| {
                    body.get(trace.len())
                        .cloned()
                        .map_or(ThreadNext::Finished, ThreadNext::Next)
                })
                .collect()
        }
    }
    fn send(dst: Tid, value: &str, lo: u64, hi: u64) -> Label {
        Label::send_within(Model::Asyn, dst, value, Window::new(lo, hi))
    }
    fn recv() -> Label {
        Label::recv(Pred::any())
    }

    #[test]
    fn valid_terminal_is_a_witness_not_a_certificate() {
        let p = Seq(vec![vec![]]);
        let answer = certify_no_escape(
            &p,
            &ExecutionGraph::new(),
            &[0],
            false,
            OwnershipBudget {
                max_states: 1,
                max_added_events: 0,
            },
        );
        assert!(matches!(answer, OwnershipCheck::FeasibleTerminal { .. }));
        assert_eq!(answer.stats().forward_terminals, 1);
        assert_eq!(answer.stats().added_events, 0);
    }

    #[test]
    fn future_send_with_canonical_revisit_keeps_obligation_alive() {
        let late = send(1, "late", 10, 10);
        let early = send(1, "early", 1, 1);
        let p = Seq(vec![vec![late.clone()], vec![recv()], vec![early]]);
        let mut g = ExecutionGraph::new();
        let late = g.add_event(0, late);
        let r = g.add_event(1, recv());
        g.set_rf(r, Some(late));
        let answer = certify_no_escape(&p, &g, &[0, 1, 2], false, OwnershipBudget::default());
        let OwnershipCheck::Unknown {
            reason: OwnershipUnknown::OutstandingRevisit(obligation),
            ..
        } = answer
        else {
            panic!("an infeasible forward completion must not hide a valid revisit");
        };
        assert_eq!(obligation.receive, r);
        assert!(crate::time::eager_feasible(&obligation.target));
    }

    fn relay_target() -> (Seq, ExecutionGraph) {
        let p = Seq(vec![
            vec![recv()],
            vec![send(0, "a", 0, 20)],
            vec![recv(), send(0, "early", 0, 0)],
            vec![send(2, "red", 1, 1), send(2, "blue", 1, 1)],
            vec![recv(), send(0, "slow", 0, 0)],
            vec![send(4, "x", 10, 10)],
        ]);
        let mut g = ExecutionGraph::new();
        let a = g.add_event(1, p.0[1][0].clone());
        g.add_event(3, p.0[3][0].clone());
        g.add_event(3, p.0[3][1].clone());
        let x = g.add_event(5, p.0[5][0].clone());
        let r = g.add_event(0, recv());
        g.set_rf(r, Some(a));
        let rx = g.add_event(4, recv());
        g.set_rf(rx, Some(x));
        let slow = g.add_event(4, p.0[4][1].clone());
        g.set_rf(r, Some(slow));
        (p, g)
    }

    #[test]
    fn common_effect_relay_has_exhaustive_no_escape_certificate() {
        let (p, g) = relay_target();
        assert!(crate::time::eager_feasible(&g));
        for des in [false, true] {
            let answer =
                certify_no_escape(&p, &g, &[0, 1, 2, 3, 4, 5], des, OwnershipBudget::default());
            let OwnershipCheck::Certified(certificate) = answer else {
                panic!("both relay choices are barren and their early revisits are noncanonical");
            };
            assert!(certificate.applies_to(&g, &[0, 1, 2, 3, 4, 5], des));
            assert!(!certificate.applies_to(&g, &[5, 4, 3, 2, 1, 0], des));
            assert_eq!(certificate.stats().forward_terminals, 2);
            assert_eq!(certificate.stats().revisit_candidates, 2);
        }
    }

    #[test]
    fn budget_exhaustion_never_certifies() {
        let (p, g) = relay_target();
        for budget in [
            OwnershipBudget {
                max_states: 0,
                max_added_events: 64,
            },
            OwnershipBudget {
                max_states: 2,
                max_added_events: 64,
            },
            OwnershipBudget {
                max_states: 128,
                max_added_events: 0,
            },
            OwnershipBudget {
                max_states: 128,
                max_added_events: 1,
            },
        ] {
            assert!(matches!(
                certify_no_escape(&p, &g, &[0, 1, 2, 3, 4, 5], true, budget),
                OwnershipCheck::Unknown { .. }
            ));
        }
    }

    #[test]
    fn certificate_requires_same_stamps_and_predicate_objects() {
        let (p, g) = relay_target();
        let priorities = [0, 1, 2, 3, 4, 5];
        let OwnershipCheck::Certified(certificate) =
            certify_no_escape(&p, &g, &priorities, true, OwnershipBudget::default())
        else {
            panic!("relay should be certified");
        };
        let rebuild = |events: Vec<EventId>, fresh_predicates: bool| {
            let mut other = ExecutionGraph::new();
            for event in events {
                let label = if fresh_predicates && g.label(event).is_recv() {
                    recv()
                } else {
                    g.label(event).clone()
                };
                assert_eq!(other.add_event(event.tid, label), event);
            }
            for event in g.iter_recvs() {
                other.set_rf(event, g.reads_from(event));
            }
            other
        };
        let mut stamp_order = g.all_events();
        stamp_order.sort_by_key(|&event| g.stamp(event));
        let exact = rebuild(stamp_order.clone(), false);
        assert!(certificate.applies_to(&exact, &priorities, true));
        let new_predicates = rebuild(stamp_order, true);
        assert_eq!(g.canonical_key(), new_predicates.canonical_key());
        assert!(!certificate.applies_to(&new_predicates, &priorities, true));
        let new_stamps = rebuild(g.all_events(), false);
        assert_eq!(g.canonical_key(), new_stamps.canonical_key());
        assert!(!certificate.applies_to(&new_stamps, &priorities, true));
    }

    #[test]
    fn certificate_is_bound_to_its_source_order() {
        let (p, g) = relay_target();
        let priorities = [0, 1, 2, 3, 4, 5];
        for order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
            let OwnershipCheck::Certified(certificate) = certify_no_escape_with_order(
                &p,
                &g,
                &priorities,
                true,
                OwnershipBudget::default(),
                order,
            ) else {
                panic!("all relay sources are foreign; either order must certify");
            };
            assert!(certificate.applies_to_with_order(&g, &priorities, true, order));
            let other = match order {
                SourceOrder::EventId => SourceOrder::SelfSendFirst,
                SourceOrder::SelfSendFirst => SourceOrder::EventId,
            };
            assert!(!certificate.applies_to_with_order(&g, &priorities, true, other));
            assert_eq!(
                certificate.applies_to(&g, &priorities, true),
                order == SourceOrder::EventId
            );
        }
    }

    #[test]
    fn coverage_uses_the_same_order_as_the_main_canonical_arm() {
        let remote = send(1, "remote", 10, 10);
        let local = send(1, "local", 1, 1);
        let receive = recv();
        let p = Seq(vec![
            vec![remote.clone()],
            vec![local.clone(), receive.clone()],
            vec![send(1, "repair", 0, 0)],
        ]);
        let mut g = ExecutionGraph::new();
        let held = g.add_event(0, remote);
        g.add_event(1, local);
        let r = g.add_event(1, receive);
        g.set_rf(r, Some(held));
        assert!(!crate::time::eager_feasible(&g));
        assert!(matches!(
            certify_no_escape(&p, &g, &[0, 1, 2], true, OwnershipBudget::default()),
            OwnershipCheck::Unknown {
                reason: OwnershipUnknown::OutstandingRevisit(_),
                ..
            }
        ));
        assert!(matches!(
            certify_no_escape_with_order(
                &p,
                &g,
                &[0, 1, 2],
                true,
                OwnershipBudget::default(),
                SourceOrder::SelfSendFirst,
            ),
            OwnershipCheck::Certified(_)
        ));
    }

    #[test]
    fn nonblocking_bottom_is_an_unresolved_construction_escape() {
        let nb = Label::recv_nb(Pred::any());
        let p = Seq(vec![vec![nb.clone()], vec![send(0, "x", 1, 1)]]);
        let mut g = ExecutionGraph::new();
        let r = g.add_event(0, nb);
        g.set_rf(r, None);
        assert!(matches!(
            certify_no_escape(&p, &g, &[0, 1], false, OwnershipBudget::default()),
            OwnershipCheck::Unknown {
                reason: OwnershipUnknown::OutstandingRevisit(_),
                ..
            }
        ));
    }

    #[test]
    fn unsupported_speculative_models_refuse_before_timing_check() {
        for model in [Model::Cd, Model::Mbox] {
            let late = send(1, "late", 10, 10);
            let early = send(1, "early", 1, 1);
            let unsupported = Label::send(model, 0, "other");
            let p = Seq(vec![
                vec![late.clone()],
                vec![recv()],
                vec![early.clone()],
                vec![unsupported.clone()],
            ]);
            let mut g = ExecutionGraph::new();
            let source = g.add_event(0, late);
            g.add_event(2, early);
            let r = g.add_event(1, recv());
            g.set_rf(r, Some(source));
            assert!(!crate::time::eager_feasible(&g));
            let priorities = [0, 1, 2, 3];
            assert!(matches!(
                certify_no_escape(&p, &g, &priorities, false, OwnershipBudget::default()),
                OwnershipCheck::Unknown {
                    reason: OwnershipUnknown::UnsupportedModel { .. },
                    ..
                }
            ));
            g.add_event(3, unsupported);
            assert!(matches!(
                certify_no_escape(&p, &g, &priorities, true, OwnershipBudget::default()),
                OwnershipCheck::Unknown {
                    reason: OwnershipUnknown::UnsupportedModel { .. },
                    ..
                }
            ));
        }
    }
}
