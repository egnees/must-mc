//! Temporal pruning from commitments that original MUST cannot remove or rewrite.
//!
//! The core is re-derived from the current graph, never inherited from an unrelated DFS
//! sibling. Canonical rules remain unchanged. A bounded deterministic continuation of
//! that core supplies additional events present in every terminal descendant. Only an
//! infeasible proof graph licenses pruning; failure to find a conflict leaves exploration.
//! Legacy timing assumes whole-program Asyn/P2p. Explicit mailbox timing also supports
//! Mbox and uses only anchors whose structural proof extends to global mailbox order.
//! Nonancestral smaller-source trials remain restricted to legacy Asyn/P2p semantics.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::consistency::consistent;
use crate::event::{EventId, Label, Model};
use crate::explorer::source_order::SourceOrder;
use crate::graph::ExecutionGraph;
use crate::observer::{FrozenTimeEvent, FrozenTimeOutcome};
use crate::program::{Program, ThreadNext};
use crate::scheduler::traces_of;

type Core = BTreeSet<EventId>;

struct Entry {
    core: ExecutionGraph,
    budget: usize,
    feasible: bool,
    mailbox_time: bool,
}

/// One bounded cache entry per worker. The program must be constant for its lifetime.
/// The key includes exact core labels, RF, ND, and predicate objects. Stamps are not part
/// of the temporal result, but core ownership is freshly proved before every cache lookup.
#[derive(Default)]
pub(crate) struct FrozenCache {
    entry: Option<Entry>,
}

impl FrozenCache {
    #[cfg(test)]
    pub(crate) fn check<P: Program>(
        &mut self,
        g: &ExecutionGraph,
        program: &P,
        max_added_events: usize,
        source_order: SourceOrder,
    ) -> FrozenTimeEvent {
        self.check_with_time_semantics(g, program, max_added_events, source_order, false)
    }

    pub(crate) fn check_with_time_semantics<P: Program>(
        &mut self,
        g: &ExecutionGraph,
        program: &P,
        max_added_events: usize,
        source_order: SourceOrder,
        mailbox_time: bool,
    ) -> FrozenTimeEvent {
        let mut report = FrozenTimeEvent {
            outcome: FrozenTimeOutcome::Unsupported,
            cache_hit: false,
            solver_calls: 0,
            core_events: 0,
            mandatory_events: 0,
            blocker_trials: 0,
            program_steps: 0,
            source_checks: 0,
            source_prunes: 0,
            source_solver_calls: 0,
            source_core_events: 0,
            source_program_steps: 0,
            source_tails: 0,
            source_future_queries: 0,
        };
        // Timing support is independent of the semantic-lookahead layer's narrower scope.
        if g.num_threads() > program.num_threads()
            || g.iter_sends()
                .any(|s| unsupported_model(g.send_model(s), mailbox_time))
        {
            return report;
        }
        let Some(core) =
            derive_core_for_semantics(g, &mut report.blocker_trials, source_order, mailbox_time)
        else {
            return report;
        };
        report.core_events = core.iter_events().count();
        if let Some(entry) = &self.entry {
            if entry.budget == max_added_events
                && entry.mailbox_time == mailbox_time
                && same_temporal_support(&entry.core, &core)
            {
                report.cache_hit = true;
                report.outcome = outcome(entry.feasible);
                if entry.feasible {
                    refute_first_alteration_sources(g, &core, program, &mut report, mailbox_time);
                }
                return report;
            }
        }
        let mut proof = core.clone();
        let mut traces = traces_of(&proof, program.num_threads());
        'threads: for (tid, trace) in traces.iter_mut().enumerate() {
            loop {
                // A partial deterministic drain is still mandatory; exhaustion does not
                // prevent a conflict already present in this partial proof from being used.
                if report.mandatory_events >= max_added_events {
                    break 'threads;
                }
                report.program_steps += 1;
                let next = program.next_thread(tid, trace);
                let (label, value) = match next {
                    ThreadNext::Next(Label::Send { model, .. })
                        if unsupported_model(Some(model), mailbox_time) =>
                    {
                        return report
                    }
                    ThreadNext::Next(label @ (Label::Send { .. } | Label::Error { .. })) => {
                        (label, None)
                    }
                    ThreadNext::Next(label @ Label::Nondet { .. }) => {
                        let Label::Nondet { set } = &label else {
                            unreachable!()
                        };
                        if set.len() != 1 {
                            break;
                        }
                        let value = set[0];
                        (label, Some(value))
                    }
                    // No receive is guessed, including a nonblocking bottom choice.
                    _ => break,
                };
                let event = proof.add_event(tid, label);
                if let Some(value) = value {
                    proof.set_nd(event, value);
                }
                trace.push(value);
                report.mandatory_events += 1;
            }
        }
        debug_assert!(
            consistent(&proof),
            "mandatory graph preserves a consistent causal core"
        );
        report.solver_calls = 1;
        let feasible = temporal_feasible(&proof, mailbox_time);
        report.outcome = outcome(feasible);
        if feasible {
            refute_first_alteration_sources(g, &core, program, &mut report, mailbox_time);
        }
        self.entry = Some(Entry {
            core,
            budget: max_added_events,
            feasible,
            mailbox_time,
        });
        report
    }
}

/// Discharge every possible sender of the first future cut that changes an old event.
/// Until that first change, old tails are unchanged. Its fresh revisiting source makes
/// its whole causal prefix irrevocable, including its sender's old tail and the already
/// immutable core. If each such union is infeasible, every first escape is barren. A
/// continuation with no old change retains the raw conflict in the entire old graph.
///
/// This does not process existing sends: their backward loops belong to ancestor calls,
/// outside the Visit being certified. No future receive or scheduling choice is guessed.
fn refute_first_alteration_sources<P: Program>(
    g: &ExecutionGraph,
    core: &ExecutionGraph,
    program: &P,
    report: &mut FrozenTimeEvent,
    mailbox_time: bool,
) {
    let graph_events = g.iter_events().count();
    if graph_events == report.core_events {
        // The just-verified (possibly drained) core already proves this graph feasible.
        return;
    }
    report.source_checks = 1;
    report.source_solver_calls += 1;
    report.source_core_events += graph_events;
    if temporal_feasible(g, mailbox_time) {
        return;
    }
    let core_ids: Core = core.iter_events().collect();
    let traces = traces_of(g, program.num_threads());
    for (tid, trace) in traces.iter().enumerate() {
        report.source_program_steps += 1;
        let ThreadNext::Next(head) = program.next_thread(tid, trace) else {
            continue;
        };
        if unsupported_model(head.model(), mailbox_time) {
            report.outcome = FrozenTimeOutcome::Unsupported;
            return;
        }
        report.source_tails += 1;
        report.source_future_queries += 1;
        if let Some(future) = program.possible_future(tid, trace) {
            // A sound no-send summary rules this thread out as a future revisiting
            // sender even if it still receives or reports errors. Validate the readily
            // checkable head condition; a missing/unknown declaration gives no exemption.
            if future.first() == Some(&head)
                && !future
                    .iter()
                    .any(|label| matches!(label, Label::Send { .. }))
            {
                continue;
            }
        }
        let mut support = core_ids.clone();
        if g.thread_len(tid) > 0 {
            let tail = EventId::new(tid, g.thread_len(tid) - 1);
            support.extend(g.porf_prefix(tail));
            support.insert(tail);
        }
        if support.len() == graph_events {
            // This union is the old graph already refuted above.
            continue;
        }
        if support.len() == core_ids.len() {
            // The feasible base core cannot refute this possible sender (including
            // an unfinished thread that has not emitted its first event yet).
            return;
        }
        let obligation = g.restrict(&support);
        report.source_solver_calls += 1;
        report.source_core_events += support.len();
        if temporal_feasible(&obligation, mailbox_time) {
            return;
        }
    }
    report.source_prunes = 1;
    report.outcome = FrozenTimeOutcome::Pruned;
}

fn unsupported_model(model: Option<Model>, mailbox_time: bool) -> bool {
    model == Some(Model::Cd) || (!mailbox_time && model == Some(Model::Mbox))
}

fn temporal_feasible(g: &ExecutionGraph, mailbox_time: bool) -> bool {
    if mailbox_time {
        // Same verdict as `check_mailbox(..).is_feasible()`, witness tables skipped.
        crate::time::eager_mailbox_feasible(g)
    } else {
        crate::time::check(g).is_feasible()
    }
}

fn outcome(feasible: bool) -> FrozenTimeOutcome {
    if feasible {
        FrozenTimeOutcome::Feasible
    } else {
        FrozenTimeOutcome::Pruned
    }
}

fn protect(g: &ExecutionGraph, core: &mut Core, event: EventId) {
    core.extend(g.porf_prefix(event));
    core.insert(event);
}

/// Irrevocable roots, permanent prefixes, and mutually supported canonical blockers.
#[cfg(test)]
fn derive_core(
    g: &ExecutionGraph,
    blocker_trials: &mut usize,
    source_order: SourceOrder,
) -> Option<ExecutionGraph> {
    derive_core_for_semantics(g, blocker_trials, source_order, false)
}

fn derive_core_for_semantics(
    g: &ExecutionGraph,
    blocker_trials: &mut usize,
    source_order: SourceOrder,
    mailbox_time: bool,
) -> Option<ExecutionGraph> {
    let first_receive = g.iter_recvs().map(|r| g.stamp(r)).min().unwrap_or(u64::MAX);
    let mut core: Core = g
        .iter_events()
        .filter(|&e| g.stamp(e) < first_receive)
        .collect();
    for event in g.iter_events() {
        match g.label(event) {
            Label::Recv { blocking, .. } => {
                if let Some(source) = g.reads_from(event) {
                    if !blocking {
                        // Original line 18 forbids deleting or revisiting this nonbottom read.
                        protect(g, &mut core, event);
                    }
                    if g.stamp(source) > g.stamp(event) {
                        // Original backward construction: the later-stamped send is irrevocable.
                        // Older protected sends whose reader changed survive inside its ancestry.
                        protect(g, &mut core, source);
                    }
                }
            }
            Label::Nondet { set } => {
                let minimum = set
                    .iter()
                    .min_by(|a, b| crate::intern::resolve(**a).cmp(crate::intern::resolve(**b)))?;
                let value = g.nd_value(event)?;
                if !set.contains(value) {
                    return None;
                }
                if value != minimum {
                    // Original line 19 forbids deleting this nonminimum choice.
                    protect(g, &mut core, event);
                }
            }
            _ => {}
        }
    }
    loop {
        loop {
            let before = core.len();
            // A cut starts at a receive. Every receive before this boundary is already
            // irrevocable, so no admitted cut can remove an earlier-stamped event.
            let boundary = g
                .iter_recvs()
                .filter(|r| !core.contains(r))
                .map(|r| g.stamp(r))
                .min()
                .unwrap_or(u64::MAX);
            for event in g.iter_events().filter(|&e| g.stamp(e) < boundary) {
                protect(g, &mut core, event);
            }
            for r in g.iter_recvs() {
                if !core.contains(&r)
                    && permanent_blocker_for_semantics(
                        g,
                        r,
                        &core,
                        blocker_trials,
                        source_order,
                        mailbox_time,
                    )
                {
                    protect(g, &mut core, r);
                }
            }
            if core.len() == before {
                break;
            }
        }

        // Greatest fixed point: these receives may protect one another's smaller
        // alternatives. Before the first change to any survivor, every supporting
        // causal core is unchanged. At that first cut the old Previous still contains
        // its earlier-stamped blocker, even if other survivors would be deleted by the
        // same cut, so original canonical line 22 rejects that cut.
        let mut candidates: Core = g
            .iter_recvs()
            .filter(|r| {
                !core.contains(r) && matches!(g.label(*r), Label::Recv { blocking: true, .. })
            })
            .collect();
        loop {
            let mut support = core.clone();
            for &r in &candidates {
                protect(g, &mut support, r);
            }
            let rejected: Vec<_> = candidates
                .iter()
                .copied()
                .filter(|&r| {
                    !permanent_blocker_for_semantics(
                        g,
                        r,
                        &support,
                        blocker_trials,
                        source_order,
                        mailbox_time,
                    )
                })
                .collect();
            if rejected.is_empty() {
                break;
            }
            for r in rejected {
                candidates.remove(&r);
            }
        }
        if candidates.is_empty() {
            break;
        }
        for r in candidates {
            protect(g, &mut core, r);
        }
    }
    let result = g.restrict(&core);
    debug_assert!(consistent(&result), "frozen graph must be a causal prefix");
    Some(result)
}

#[cfg(test)]
fn permanent_blocker(
    g: &ExecutionGraph,
    r: EventId,
    core: &Core,
    trials: &mut usize,
    source_order: SourceOrder,
) -> bool {
    permanent_blocker_for_semantics(g, r, core, trials, source_order, false)
}

fn permanent_blocker_for_semantics(
    g: &ExecutionGraph,
    r: EventId,
    core: &Core,
    trials: &mut usize,
    source_order: SourceOrder,
    mailbox_time: bool,
) -> bool {
    if !matches!(g.label(r), Label::Recv { blocking: true, .. }) {
        return false;
    }
    let Some(held) = g.reads_from(r) else {
        return false;
    };
    let ancestors = g.porf_prefix(r);
    ancestors.union(core).any(|&m| {
        if g.stamp(m) >= g.stamp(r)
            || !matches!(g.send_model(m), Some(Model::Asyn | Model::P2p))
            || !g.matches(m, r)
            || g.iter_recvs()
                .any(|q| q.tid == r.tid && q.idx < r.idx && g.reads_from(q) == Some(m))
        {
            return false;
        }
        if source_order.key(g, m) >= source_order.key(g, held) {
            return false;
        }
        if ancestors.contains(&m) && g.send_model(m) == Some(Model::Asyn) {
            return true;
        }
        // A future Mbox send may introduce a global send-order consistency cycle.
        // The local Asyn/P2p trial below does not prove its absence. The ancestral
        // Asyn case above only removes causal/order obligations, so remains valid.
        if mailbox_time {
            return false;
        }
        // The source's clock/causal prefix and the receiver's prefix are fixed. This local
        // trial establishes the P2p ordering and cycle conditions for every later Previous.
        let mut support = ancestors.clone();
        support.insert(r);
        support.extend(g.porf_prefix(m));
        support.insert(m);
        let mut trial = g.restrict(&support);
        trial.set_rf(r, Some(m));
        *trials += 1;
        consistent(&trial)
    })
}

fn same_temporal_support(a: &ExecutionGraph, b: &ExecutionGraph) -> bool {
    a.num_threads() == b.num_threads()
        && a.iter_events().count() == b.iter_events().count()
        && a.iter_events().all(|e| {
            b.contains(e)
                && a.label(e) == b.label(e)
                && a.reads_from(e) == b.reads_from(e)
                && a.nd_value(e) == b.nd_value(e)
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

    struct Seq(Vec<Vec<Label>>);
    impl Program for Seq {
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
    fn send(model: Model, dst: usize, value: &str, delay: u64) -> Label {
        Label::send_within(model, dst, value, Window::new(delay, delay))
    }
    fn timer_graph() -> (Seq, ExecutionGraph, EventId) {
        let timer = send(Model::Asyn, 0, "timer", 10);
        let rpc = send(Model::P2p, 0, "rpc", 20);
        let recv = Label::recv(Pred::any());
        let p = Seq(vec![vec![timer.clone(), recv.clone()], vec![rpc.clone()]]);
        let mut g = ExecutionGraph::new();
        g.add_event(0, timer);
        let source = g.add_event(1, rpc);
        let r = g.add_event(0, recv);
        g.set_rf(r, Some(source));
        (p, g, r)
    }
    #[test]
    fn late_rpc_frozen_by_earlier_local_timer_prunes_and_caches() {
        let (p, g, r) = timer_graph();
        let mut cache = FrozenCache::default();
        let first = cache.check(&g, &p, 32, SourceOrder::EventId);
        assert!(matches!(first.outcome, FrozenTimeOutcome::Pruned));
        assert_eq!(first.solver_calls, 1);
        assert!(!first.cache_hit);
        let second = cache.check(&g, &p, 32, SourceOrder::EventId);
        assert!(matches!(second.outcome, FrozenTimeOutcome::Pruned));
        assert_eq!(second.solver_calls, 0);
        assert!(second.cache_hit);
        let mut changed = g;
        changed.set_rf(r, Some(EventId::new(0, 0)));
        let third = cache.check(&changed, &p, 32, SourceOrder::EventId);
        assert!(!third.cache_hit);
        assert!(matches!(third.outcome, FrozenTimeOutcome::Feasible));
    }
    #[test]
    fn fresh_predicate_objects_are_not_cache_equivalent() {
        let (p, g, _) = timer_graph();
        let mut cache = FrozenCache::default();
        cache.check(&g, &p, 32, SourceOrder::EventId);
        let mut same = ExecutionGraph::new();
        same.add_event(0, g.label(EventId::new(0, 0)).clone());
        let source = same.add_event(1, g.label(EventId::new(1, 0)).clone());
        let r = same.add_event(0, Label::recv(Pred::any()));
        same.set_rf(r, Some(source));
        assert_eq!(g.canonical_key(), same.canonical_key());
        assert!(!cache.check(&same, &p, 32, SourceOrder::EventId).cache_hit);
    }
    #[test]
    fn mandatory_future_send_can_refute_a_feasible_frozen_core() {
        let recv = Label::recv(Pred::any());
        let nd = Label::nondet(["a", "b"]);
        let slow = send(Model::Asyn, 0, "slow", 10);
        let early = send(Model::Asyn, 0, "early", 1);
        let p = Seq(vec![
            vec![recv.clone(), nd.clone()],
            vec![slow.clone()],
            vec![early],
        ]);
        let mut g = ExecutionGraph::new();
        let source = g.add_event(1, slow);
        let r = g.add_event(0, recv);
        g.set_rf(r, Some(source));
        let e = g.add_event(0, nd);
        g.set_nd(e, "b".into());
        assert!(crate::time::check(&g).is_feasible());
        let mut cache = FrozenCache::default();
        let limited = cache.check(&g, &p, 0, SourceOrder::EventId);
        assert!(matches!(limited.outcome, FrozenTimeOutcome::Feasible));
        let full = cache.check(&g, &p, 8, SourceOrder::EventId);
        assert!(matches!(full.outcome, FrozenTimeOutcome::Pruned));
        assert_eq!(full.mandatory_events, 1);
        assert!(!full.cache_hit);
    }
    #[test]
    fn mandatory_drain_never_guesses_nonblocking_bottom() {
        let recv = Label::recv(Pred::any());
        let nd = Label::nondet(["a", "b"]);
        let slow = send(Model::Asyn, 0, "slow", 10);
        let early = send(Model::Asyn, 0, "early", 1);
        let p = Seq(vec![
            vec![recv.clone(), nd.clone()],
            vec![slow.clone()],
            vec![Label::recv_nb(Pred::any()), early],
        ]);
        let mut g = ExecutionGraph::new();
        let source = g.add_event(1, slow);
        let r = g.add_event(0, recv);
        g.set_rf(r, Some(source));
        let e = g.add_event(0, nd);
        g.set_nd(e, "b".into());
        let got = FrozenCache::default().check(&g, &p, 8, SourceOrder::EventId);
        assert!(matches!(got.outcome, FrozenTimeOutcome::Feasible));
        assert_eq!(got.mandatory_events, 0);
    }

    #[test]
    fn frozen_receives_advance_the_permanent_stamp_prefix() {
        let mut g = ExecutionGraph::new();
        let source = g.add_event(1, send(Model::Asyn, 0, "first", 1));
        let frozen = g.add_event(0, Label::recv_nb(Pred::any()));
        g.set_rf(frozen, Some(source));
        let middle = g.add_event(2, send(Model::Asyn, 3, "second", 1));
        let frontier = g.add_event(3, Label::recv(Pred::any()));
        g.set_rf(frontier, Some(middle));
        let after = g.add_event(2, send(Model::Asyn, 0, "after", 1));
        let core = derive_core(&g, &mut 0, SourceOrder::EventId).unwrap();
        assert!(core.contains(middle));
        assert!(!core.contains(frontier));
        assert!(!core.contains(after));

        // Freezing the last receive removes the last possible cut boundary, so even
        // events outside its causal ancestry now belong to the permanent prefix.
        let choice = g.add_event(3, Label::nondet(["a", "b"]));
        g.set_nd(choice, "b".into());
        let core = derive_core(&g, &mut 0, SourceOrder::EventId).unwrap();
        assert!(core.contains(after));
        assert_eq!(core.iter_events().count(), g.iter_events().count());
    }

    fn mutually_blocking_graph(selective: bool) -> (ExecutionGraph, EventId, EventId) {
        let mut g = ExecutionGraph::new();
        // This mutable receive prevents the initial permanent prefix from reaching
        // either smaller source; neither receiver has its own ancestral alternative.
        g.add_event(3, Label::recv_nb(Pred::any()));
        g.add_event(0, send(Model::Asyn, 1, "m0", 1));
        g.add_event(1, send(Model::Asyn, 0, "m1", 1));
        let u0 = g.add_event(2, send(Model::Asyn, 0, "u0", 10));
        let u1 = g.add_event(2, send(Model::Asyn, 1, "u1", 10));
        let r0 = g.add_event(
            0,
            Label::recv(if selective {
                Pred::eq("u0")
            } else {
                Pred::any()
            }),
        );
        g.set_rf(r0, Some(u0));
        let r1 = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(r1, Some(u1));
        (g, r0, r1)
    }

    #[test]
    fn mutual_blockers_freeze_without_an_initial_immutable_source() {
        let (g, r0, r1) = mutually_blocking_graph(false);
        assert!(consistent(&g));
        let mut trials = 0;
        assert!(!permanent_blocker(
            &g,
            r0,
            &Core::new(),
            &mut trials,
            SourceOrder::EventId
        ));
        assert!(!permanent_blocker(
            &g,
            r1,
            &Core::new(),
            &mut trials,
            SourceOrder::EventId
        ));
        let core = derive_core(&g, &mut trials, SourceOrder::EventId).unwrap();
        assert!(core.contains(r0));
        assert!(core.contains(r1));
        assert!(!core.contains(EventId::new(3, 0)));
        assert!(!crate::time::check(&core).is_feasible());
    }

    #[test]
    fn mutual_blockers_remove_unsupported_receives_to_a_fixed_point() {
        let (g, r0, r1) = mutually_blocking_graph(true);
        let core = derive_core(&g, &mut 0, SourceOrder::EventId).unwrap();
        assert!(!core.contains(r0));
        // The second receive initially borrows a blocker from the first one's core;
        // losing that support must remove it on the next elimination iteration.
        assert!(!core.contains(r1));
        assert_eq!(core.iter_events().count(), 0);
    }

    #[test]
    fn self_send_order_changes_the_proved_blocker_and_revalidates_cache_support() {
        let timer = send(Model::Asyn, 1, "timer", 10);
        let rpc = send(Model::P2p, 1, "rpc", 20);
        let recv = Label::recv(Pred::any());
        let p = Seq(vec![vec![rpc.clone()], vec![timer.clone(), recv.clone()]]);
        let mut g = ExecutionGraph::new();
        let source = g.add_event(0, rpc);
        g.add_event(1, timer);
        let r = g.add_event(1, recv);
        g.set_rf(r, Some(source));
        let mut cache = FrozenCache::default();
        let original = cache.check(&g, &p, 8, SourceOrder::EventId);
        // Original ordering leaves the receiver mutable; the new sender rule can
        // still reject this already-terminal graph, after the base core was feasible.
        assert_eq!(original.source_prunes, 1);
        let ranked = cache.check(&g, &p, 8, SourceOrder::SelfSendFirst);
        assert!(matches!(ranked.outcome, FrozenTimeOutcome::Pruned));
        assert_eq!(ranked.source_prunes, 0);
        assert!(!ranked.cache_hit);
        assert_eq!(ranked.core_events, original.core_events + 1);
    }

    #[test]
    fn cached_feasible_core_does_not_cache_a_whole_graph_sender_verdict() {
        let timer = send(Model::Asyn, 0, "timer", 10);
        let early = send(Model::Asyn, 0, "early", 1);
        let recv = Label::recv(Pred::any());
        let poll = Label::recv_nb(Pred::any());
        let p = Seq(vec![
            vec![
                timer.clone(),
                recv.clone(),
                send(Model::Asyn, 1, "reply", 1),
            ],
            vec![early.clone(), poll.clone()],
        ]);
        let mut g = ExecutionGraph::new();
        let source = g.add_event(0, timer);
        g.add_event(1, early);
        let r = g.add_event(0, recv);
        g.set_rf(r, Some(source));
        assert!(!crate::time::check(&g).is_feasible());
        let mut cache = FrozenCache::default();
        let unresolved = cache.check(&g, &p, 8, SourceOrder::EventId);
        assert_eq!(unresolved.outcome, FrozenTimeOutcome::Feasible);
        assert_eq!(unresolved.source_prunes, 0);

        let mut finished_sender = g.clone();
        finished_sender.add_event(1, poll);
        let certified = cache.check(&finished_sender, &p, 8, SourceOrder::EventId);
        assert!(certified.cache_hit);
        assert_eq!(certified.solver_calls, 0);
        assert_eq!(certified.outcome, FrozenTimeOutcome::Pruned);
        assert_eq!(certified.source_prunes, 1);
        assert!(certified.source_solver_calls > 0);

        let unresolved_again = cache.check(&g, &p, 8, SourceOrder::EventId);
        assert!(unresolved_again.cache_hit);
        assert_eq!(unresolved_again.outcome, FrozenTimeOutcome::Feasible);
        assert_eq!(unresolved_again.source_prunes, 0);

        struct SendlessTail(Seq);
        impl Program for SendlessTail {
            fn num_threads(&self) -> usize {
                self.0.num_threads()
            }
            fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
                self.0.next(traces)
            }
            fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
                if tid != 1 {
                    return None;
                }
                // The remaining program on this thread is exactly one NB receive,
                // followed by termination. Its summary rules out every future send.
                Some(self.0 .0[tid][trace.len()..].to_vec())
            }
        }
        // A different program/summary contract gets a fresh cache. Knowing that the
        // still-unfinished thread never sends closes the obligation immediately.
        let declared = FrozenCache::default().check(&g, &SendlessTail(p), 8, SourceOrder::EventId);
        assert_eq!(declared.outcome, FrozenTimeOutcome::Pruned);
        assert_eq!(declared.source_prunes, 1);
        assert!(declared.source_future_queries > 0);
    }
}
