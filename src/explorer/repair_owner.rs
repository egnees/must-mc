//! A narrow, constructive certificate for removing a redundant timed revisit.
//!
//! The alternate owner is reached from the empty graph using only the explorer's forward
//! edges, in exactly the recorded insertion order. Its canonical obligations are all
//! unconditional minima. Thus rejecting backward edges with this certificate cannot remove
//! the replacement path, including when this rule is applied throughout the search.

use std::sync::Arc;

use crate::consistency::consistent;
use crate::event::{EventId, Label, Model, Tid};
use crate::graph::ExecutionGraph;
use crate::program::Program;
use crate::scheduler::{pick, traces_of, NextStep};

/// The concrete alternate send-add host and work performed by its successful replay.
/// It can be time-infeasible after the final send: the repaired target must pass the gate.
pub(super) struct OwnerWitness {
    pub(super) host: ExecutionGraph,
    pub(super) replay_events: usize,
}

/// Certify a replacement for an already-admitted level-4 timed candidate. Unknown or
/// unsupported cases return `None`, preserving the existing decision.
///
/// Scope: Asyn sends, blocking receives, finite ND, no errors; `Deleted \ {s}` consists
/// only of nondets. Reset those nondets and `r` to their unconditional canonical minima,
/// then verify the proposed owner's complete forward construction from the empty graph.
/// No search over alternative schedules or choices is performed.
///
/// The caller must use the same program and priorities as exploration and apply this only
/// after its existing candidate checks, with no early-stop assumption in its set-preservation
/// claim. The event limit bounds replay length; individual program/gate calls retain their
/// normal termination requirements.
#[allow(clippy::too_many_arguments)]
pub(super) fn certify_forward_minimum_owner<P: Program>(
    program: &P,
    priorities: &[Tid],
    g: &ExecutionGraph,
    r: EventId,
    s: EventId,
    target: &ExecutionGraph,
    max_replay_events: usize,
) -> Option<OwnerWitness> {
    let event_count = g.iter_events().count();
    if event_count > max_replay_events
        || !g.contains(r)
        || !g.contains(s)
        || !matches!(g.label(r), Label::Recv { blocking: true, .. })
        || !matches!(
            g.label(s),
            Label::Send {
                model: Model::Asyn,
                ..
            }
        )
        || g.iter_events().any(|e| {
            matches!(g.label(e), Label::Send { model, .. } if *model != Model::Asyn)
                || matches!(
                    g.label(e),
                    Label::Recv {
                        blocking: false,
                        ..
                    } | Label::Error { .. }
                )
        })
    {
        return None;
    }
    let ancestors = g.porf_prefix(s);
    if ancestors.contains(&r) || !g.matches(s, r) {
        return None;
    }
    let deleted: Vec<_> = g
        .iter_events()
        .filter(|&e| g.stamp(e) > g.stamp(r) && !ancestors.contains(&e))
        .collect();
    if !deleted.contains(&s)
        || deleted
            .iter()
            .any(|&e| e != s && !matches!(g.label(e), Label::Nondet { .. }))
    {
        return None;
    }

    let mut alternate = g.clone();
    let mut changed = false;
    for &e in &deleted {
        if e == s {
            continue;
        }
        let Label::Nondet { set } = alternate.label(e) else {
            return None;
        };
        let minimum = *set
            .iter()
            .min_by(|a, b| crate::intern::resolve(**a).cmp(crate::intern::resolve(**b)))?;
        let held = *alternate.nd_value(e)?;
        if !set.contains(&held) {
            return None;
        }
        changed |= held != minimum;
        alternate.set_nd(e, minimum);
    }

    // This is exactly Previous(r, s); candidate ordering clears r's own RF first.
    let previous_keep = alternate
        .iter_events()
        .filter(|&e| alternate.stamp(e) <= alternate.stamp(r) || ancestors.contains(&e))
        .collect();
    let previous = alternate.restrict(&previous_keep);
    let candidates = super::revisit::cons_candidates(&previous, r, true);
    let minimum_source = *candidates.first()?;
    let held_source = alternate.reads_from(r)?;
    if !candidates.contains(&held_source) {
        return None;
    }
    changed |= held_source != minimum_source;
    alternate.set_rf(r, Some(minimum_source));
    // This is also the explicit protection against deleting our own all-minimum owner.
    if !changed {
        return None;
    }

    let mut order: Vec<_> = alternate.iter_events().collect();
    order.sort_by_key(|&e| alternate.stamp(e));
    if order.last() != Some(&s) {
        return None;
    }
    let mut replay = ExecutionGraph::new();
    for e in order {
        let nexts = program.next(&traces_of(&replay, program.num_threads()));
        let NextStep::Event { tid, label } = pick(&replay, &nexts, priorities, true) else {
            return None;
        };
        if tid != e.tid || replay.thread_len(tid) != e.idx || &label != alternate.label(e) {
            return None;
        }
        // Retain the original label/predicate support. Changed choices can only have ND
        // descendants among existing events in this shape; their full option sets are
        // compared above. No retained receive predicate depends on a changed value.
        let added = replay.add_event(tid, alternate.label(e).clone());
        if replay.stamp(added) != alternate.stamp(e) {
            return None;
        }
        match alternate.label(e) {
            Label::Recv { .. } => {
                let source = alternate.reads_from(e)?;
                if !replay.contains(source) {
                    return None;
                }
                replay.set_rf(added, Some(source));
                if !consistent(&replay) || !crate::time::check(&replay).is_feasible() {
                    return None;
                }
            }
            Label::Nondet { set } => {
                let value = *alternate.nd_value(e)?;
                if !set.contains(&value) {
                    return None;
                }
                replay.set_nd(added, value);
            }
            Label::Send { .. } => {
                if !consistent(&replay) {
                    return None;
                }
                // The final send's backward revisits run even when its forward gate fails.
                if e != s && !crate::time::gate_feasible(&replay, program, priorities) {
                    return None;
                }
            }
            Label::Error { .. } => return None,
        }
    }
    if !same_graph(&replay, &alternate) || replay.is_read(s) {
        return None;
    }
    let target_keep = replay
        .iter_events()
        .filter(|&e| replay.stamp(e) <= replay.stamp(r) || ancestors.contains(&e) || e == s)
        .collect();
    let mut replacement = replay.restrict(&target_keep);
    replacement.set_rf(r, Some(s));
    if !same_graph(&replacement, target)
        || !consistent(&replacement)
        || !crate::time::gate_feasible(&replacement, program, priorities)
    {
        return None;
    }
    Some(OwnerWitness {
        host: replay,
        replay_events: event_count,
    })
}

/// Exact future-search support, including insertion stamps and predicate Arc identity.
/// Content-key equality alone does not preserve the canonical construction's context.
fn same_graph(a: &ExecutionGraph, b: &ExecutionGraph) -> bool {
    a.num_threads() == b.num_threads()
        && a.iter_events().count() == b.iter_events().count()
        && a.iter_events().all(|e| {
            b.contains(e)
                && a.label(e) == b.label(e)
                && a.reads_from(e) == b.reads_from(e)
                && a.nd_value(e) == b.nd_value(e)
                && a.stamp(e) == b.stamp(e)
                && match (a.label(e), b.label(e)) {
                    (Label::Recv { pred: x, .. }, Label::Recv { pred: y, .. }) => Arc::ptr_eq(x, y),
                    _ => true,
                }
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::{Pred, Val, Window};
    use crate::program::ThreadNext;

    struct Sequence(Vec<Vec<Label>>);
    impl Program for Sequence {
        fn num_threads(&self) -> usize {
            self.0.len()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.0
                .iter()
                .enumerate()
                .map(|(tid, labels)| {
                    labels
                        .get(traces[tid].len())
                        .cloned()
                        .map_or(ThreadNext::Finished, ThreadNext::Next)
                })
                .collect()
        }
    }

    fn fixture() -> (Sequence, ExecutionGraph, EventId, EventId, ExecutionGraph) {
        let a = Label::send_within(Model::Asyn, 0, "a", Window::new(0, 20));
        let b = Label::send_within(Model::Asyn, 0, "b", Window::new(10, 10));
        let timer = Label::send_within(Model::Asyn, 1, "timer", Window::new(5, 5));
        let r_label = Label::recv(Pred::any());
        let rg_label = Label::recv(Pred::eq("timer"));
        let s_label = Label::send_within(Model::Asyn, 0, "s", Window::new(1, 1));
        let program = Sequence(vec![
            vec![a.clone(), b.clone(), r_label.clone()],
            vec![timer.clone(), rg_label.clone(), s_label.clone()],
        ]);
        let mut g = ExecutionGraph::new();
        g.add_event(0, a);
        let timer = g.add_event(1, timer);
        let b = g.add_event(0, b);
        let r = g.add_event(0, r_label);
        g.set_rf(r, Some(b));
        let rg = g.add_event(1, rg_label);
        g.set_rf(rg, Some(timer));
        let s = g.add_event(1, s_label);
        let mut target = g.clone();
        target.set_rf(r, Some(s));
        (program, g, r, s, target)
    }

    #[test]
    fn exact_forward_owner_can_repair_an_infeasible_send_add_host() {
        let (program, g, r, s, target) = fixture();
        assert!(!crate::time::check(&g).is_feasible());
        assert!(crate::time::check(&target).is_feasible());
        let witness = certify_forward_minimum_owner(&program, &[0, 1], &g, r, s, &target, 6)
            .expect("the minimum holder has an exact forward construction");
        assert_eq!(witness.replay_events, 6);
        assert_eq!(witness.host.reads_from(r), Some(EventId::new(0, 0)));
        for e in g.iter_events() {
            assert_eq!(g.stamp(e), witness.host.stamp(e));
        }
    }

    #[test]
    fn exhausted_replay_budget_preserves_original_decision() {
        let (program, g, r, s, target) = fixture();
        for budget in [0, 5] {
            assert!(
                certify_forward_minimum_owner(&program, &[0, 1], &g, r, s, &target, budget)
                    .is_none()
            );
        }
    }

    #[test]
    fn all_minimum_replacement_is_never_rejected_by_this_rule() {
        let (program, mut g, r, s, target) = fixture();
        g.set_rf(r, Some(EventId::new(0, 0)));
        assert!(certify_forward_minimum_owner(&program, &[0, 1], &g, r, s, &target, 100).is_none());
    }
}
