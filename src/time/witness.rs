//! Opt-in evidence for the existing viability oracle.
//!
//! [`query`] runs the same drain, cuts, and choice order as [`super::viable`]. A successful
//! result owns the actual quiescent graph at the oracle's success test. It is evidence of
//! that test, **not** a terminal execution, a canonical owner, or a completeness certificate.
//! Positive boolean memo entries are reconstructed; they never stand in for a graph.
//!
//! Budgets bound visited search nodes and graph additions across the entire query. They do
//! not interrupt one `Program` call, consistency check, forced closure, or time-solver call.
//! The usual finite-program and sound-future contracts therefore still apply.

use std::convert::Infallible;

use crate::event::{EventId, Label, Tid, Val};
use crate::graph::ExecutionGraph;
use crate::program::{Program, ThreadNext};
use crate::scheduler::traces_of;

use super::ViableMemo;

/// The one existing choice re-pinned by an oracle call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PinnedChoice {
    Nondet {
        event: EventId,
        value: Val,
    },
    Receive {
        event: EventId,
        source: Option<EventId>,
    },
}

impl PinnedChoice {
    fn apply(self, graph: &mut ExecutionGraph) {
        match self {
            Self::Nondet { event, value } => {
                assert!(graph.contains(event), "ND pin must name an existing event");
                let Label::Nondet { set } = graph.label(event) else {
                    panic!("ND pin must name a nondeterministic choice");
                };
                assert!(
                    set.contains(&value),
                    "ND pin value must belong to its option set"
                );
                graph.set_nd(event, value);
            }
            Self::Receive { event, source } => {
                assert!(
                    graph.contains(event) && graph.label(event).is_recv(),
                    "receive pin must name an existing receive"
                );
                if let Some(source) = source {
                    assert!(
                        graph.contains(source) && graph.label(source).is_send(),
                        "receive pin source must name an existing send"
                    );
                }
                graph.set_rf(event, source);
            }
        }
    }
}

/// Limits on diagnostic work, shared by all alternatives rather than reset per branch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleBudget {
    pub max_states: usize,
    pub max_added_events: usize,
}

impl Default for OracleBudget {
    fn default() -> Self {
        Self {
            max_states: 10_000,
            max_added_events: 10_000,
        }
    }
}

/// Work performed by this diagnostic query, including failed alternatives.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OracleStats {
    /// Entered DFS nodes, including cache hits and reconstructed positive hits.
    pub states: usize,
    /// Calls to `add_event`, including branch templates even if no option is consistent.
    pub added_events: usize,
    /// Of `added_events`, sends, errors, and singleton nondets added by the drain.
    pub drain_added: usize,
    /// Quiescent nodes reaching the choice loop after all cuts and the success test.
    pub branch_states: usize,
    /// Recursive choice calls attempted; an exhausted state budget may stop at entry.
    pub branch_children: usize,
    pub positive_cache_reconstructions: usize,
    pub negative_cache_hits: usize,
    /// The pinned entry graph already contains the target position.
    pub target_present_on_entry: bool,
    /// The target is absent, exactly next on its process, and has the requested label.
    pub target_initially_ready: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OracleLimit {
    States,
    AddedEvents,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleUnknown {
    pub limit: OracleLimit,
    pub stats: OracleStats,
}

/// Concrete evidence produced only at the shared oracle's actual success test.
#[derive(Clone, Debug)]
pub struct OracleWitness {
    base: ExecutionGraph,
    choice: PinnedChoice,
    target: EventId,
    target_label: Label,
    priorities: Vec<Tid>,
    graph: ExecutionGraph,
    stats: OracleStats,
}

impl OracleWitness {
    pub fn base(&self) -> &ExecutionGraph {
        &self.base
    }
    pub fn choice(&self) -> PinnedChoice {
        self.choice
    }
    pub fn target(&self) -> EventId {
        self.target
    }
    pub fn target_label(&self) -> &Label {
        &self.target_label
    }
    pub fn priorities(&self) -> &[Tid] {
        &self.priorities
    }
    pub fn graph(&self) -> &ExecutionGraph {
        &self.graph
    }
    pub fn stats(&self) -> OracleStats {
        self.stats
    }

    /// Recheck the success predicate without using either memo. Also replay each process's
    /// labels from its own trace and check that no forced drain event remains. This does not
    /// establish canonical reachability or terminality, and uses the same `Program` and
    /// predicate-identity contracts as the boolean oracle.
    pub fn recheck<P: Program>(&self, program: &P) -> bool {
        let g = &self.graph;
        if g.num_threads() > program.num_threads()
            || self.target.tid >= program.num_threads()
            || !g.contains(self.target)
            || g.label(self.target) != &self.target_label
            || g.is_read(self.target)
            || !crate::consistency::consistent(g)
        {
            return false;
        }
        let traces = traces_of(g, program.num_threads());
        for e in g.iter_events() {
            if let Label::Nondet { set } = g.label(e) {
                if !g.nd_value(e).is_some_and(|value| set.contains(value)) {
                    return false;
                }
            }
            if e.tid >= traces.len()
                || program.next_thread(e.tid, &traces[e.tid][..e.idx]).label() != Some(g.label(e))
            {
                return false;
            }
        }
        let quiescent = program.next(&traces).iter().all(|next| match next {
            ThreadNext::Next(Label::Send { .. } | Label::Error { .. }) => false,
            ThreadNext::Next(Label::Nondet { set }) => set.len() != 1,
            _ => true,
        });
        quiescent && super::gate_feasible(g, program, &self.priorities)
    }
}

#[derive(Clone, Debug)]
// Keep witnesses inline: boxing would add an allocation to each oracle success.
#[allow(clippy::large_enum_variant)]
pub enum OracleOutcome {
    Witness(OracleWitness),
    /// The existing oracle's search returned false; this is not a proof that no semantic
    /// continuation or canonical owner exists outside that search's success predicate.
    NotViable(OracleStats),
    Unknown(OracleUnknown),
}

impl OracleOutcome {
    pub fn stats(&self) -> OracleStats {
        match self {
            Self::Witness(witness) => witness.stats,
            Self::NotViable(stats) => *stats,
            Self::Unknown(unknown) => unknown.stats,
        }
    }
    pub fn verdict(&self) -> Option<bool> {
        match self {
            Self::Witness(_) => Some(true),
            Self::NotViable(_) => Some(false),
            Self::Unknown(_) => None,
        }
    }
}

/// Diagnose one ND, RF, or bottom oracle call. The base and its existing graph are unchanged.
///
/// The pin must name an existing event of the right kind, an ND value must belong to that
/// event's option set, and any RF source must be an existing send. Invalid pins panic.
/// The retained base must be replay-valid under the chosen pin, with all other ND values
/// assigned to valid options; downstream labels depending on a changed choice must already
/// have been removed by the caller. Also `target.tid < program.num_threads()`. The memo
/// must belong to this same program, priorities, and predicate interpretation. In particular,
/// do not reuse a memo across programs merely because their printable labels coincide.
///
/// A positive cache hit is searched again until a concrete successful graph is found.
/// Budget exhaustion propagates as `Unknown`; incomplete nodes are never cached as false.
/// Completed subproblems and gate checks may still populate the caller's memo.
#[allow(clippy::too_many_arguments)]
pub fn query<P: Program>(
    base: &ExecutionGraph,
    choice: PinnedChoice,
    program: &P,
    priorities: &[Tid],
    target: EventId,
    target_label: &Label,
    memo: &mut ViableMemo,
    budget: OracleBudget,
) -> OracleOutcome {
    let mut pinned = base.clone();
    choice.apply(&mut pinned);
    let present = pinned.contains(target);
    let initially_ready = !present
        && pinned.thread_len(target.tid) == target.idx
        && program
            .next_thread(
                target.tid,
                &traces_of(&pinned, program.num_threads())[target.tid],
            )
            .label()
            == Some(target_label);
    let mut control = Diagnostics {
        budget,
        stats: OracleStats {
            target_present_on_entry: present,
            target_initially_ready: initially_ready,
            ..OracleStats::default()
        },
        success: None,
    };
    let result = super::viable_search_with(
        pinned,
        program,
        priorities,
        target,
        target_label,
        memo,
        &mut control,
    );
    match result {
        Ok(true) => OracleOutcome::Witness(OracleWitness {
            base: base.clone(),
            choice,
            target,
            target_label: target_label.clone(),
            priorities: priorities.to_vec(),
            graph: control
                .success
                .expect("positive oracle result has concrete evidence"),
            stats: control.stats,
        }),
        Ok(false) => OracleOutcome::NotViable(control.stats),
        Err(limit) => OracleOutcome::Unknown(OracleUnknown {
            limit,
            stats: control.stats,
        }),
    }
}

/// Statically dispatched instrumentation: ordinary boolean queries allocate no diagnostic
/// state or witness and cannot exhaust a diagnostic budget (`Stop = Infallible`).
pub(super) trait SearchControl {
    type Stop;
    fn enter_state(&mut self) -> Result<(), Self::Stop>;
    fn use_cached(&mut self, verdict: bool) -> bool;
    fn add_event(&mut self, drained: bool) -> Result<(), Self::Stop>;
    fn branch_state(&mut self);
    fn branch_child(&mut self);
    fn success(&mut self, graph: &ExecutionGraph);
}

pub(super) struct NoDiagnostics;

impl SearchControl for NoDiagnostics {
    type Stop = Infallible;
    #[inline(always)]
    fn enter_state(&mut self) -> Result<(), Self::Stop> {
        Ok(())
    }
    #[inline(always)]
    fn use_cached(&mut self, _: bool) -> bool {
        true
    }
    #[inline(always)]
    fn add_event(&mut self, _: bool) -> Result<(), Self::Stop> {
        Ok(())
    }
    #[inline(always)]
    fn branch_state(&mut self) {}
    #[inline(always)]
    fn branch_child(&mut self) {}
    #[inline(always)]
    fn success(&mut self, _: &ExecutionGraph) {}
}

struct Diagnostics {
    budget: OracleBudget,
    stats: OracleStats,
    success: Option<ExecutionGraph>,
}

impl SearchControl for Diagnostics {
    type Stop = OracleLimit;
    fn enter_state(&mut self) -> Result<(), Self::Stop> {
        if self.stats.states >= self.budget.max_states {
            return Err(OracleLimit::States);
        }
        self.stats.states += 1;
        Ok(())
    }
    fn use_cached(&mut self, verdict: bool) -> bool {
        if verdict {
            self.stats.positive_cache_reconstructions += 1;
            false
        } else {
            self.stats.negative_cache_hits += 1;
            true
        }
    }
    fn add_event(&mut self, drained: bool) -> Result<(), Self::Stop> {
        if self.stats.added_events >= self.budget.max_added_events {
            return Err(OracleLimit::AddedEvents);
        }
        self.stats.added_events += 1;
        self.stats.drain_added += usize::from(drained);
        Ok(())
    }
    fn branch_state(&mut self) {
        self.stats.branch_states += 1;
    }
    fn branch_child(&mut self) {
        self.stats.branch_children += 1;
    }
    fn success(&mut self, graph: &ExecutionGraph) {
        self.success = Some(graph.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::Model;

    struct TwoEvents([Label; 2]);
    impl Program for TwoEvents {
        fn num_threads(&self) -> usize {
            1
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            vec![self
                .0
                .get(traces[0].len())
                .cloned()
                .map_or(ThreadNext::Finished, ThreadNext::Next)]
        }
    }

    #[test]
    fn success_recheck_rejects_an_invalid_nd_annotation() {
        let nd = Label::nondet(["a", "b"]);
        let goal = Label::send(Model::Asyn, 0, "goal");
        let program = TwoEvents([nd.clone(), goal.clone()]);
        let mut base = ExecutionGraph::new();
        let ep = base.add_event(0, nd);
        base.set_nd(ep, "a".into());
        let OracleOutcome::Witness(mut witness) = query(
            &base,
            PinnedChoice::Nondet {
                event: ep,
                value: "a".into(),
            },
            &program,
            &[0],
            EventId::new(0, 1),
            &goal,
            &mut ViableMemo::new(),
            OracleBudget::default(),
        ) else {
            panic!("expected witness")
        };
        assert!(witness.recheck(&program));
        // An opaque witness cannot be changed through the public API; mutate internally
        // to verify the recheck's membership guard independently from query validation.
        witness.graph.set_nd(ep, "c".into());
        assert!(!witness.recheck(&program));
    }
}
