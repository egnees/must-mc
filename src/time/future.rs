//! Bounded reasoning about semantic forward completions of a fixed graph.
//!
//! This layer does not pick a physical event order or enumerate clock valuations. It
//! drains deterministic local effects and builds a finite tree of **guarded choices**.
//! Different cases keep separate graphs, so their sends, clock origins, and receive
//! predicates are never accidentally conjoined. When every case is time-infeasible,
//! their disjunction is impossible: this also detects a common early-send effect when
//! its concrete event position differs between cases.
//!
//! A receive is expanded only after proving that its currently present sources cover
//! every possible source in a continuation. Other unfinished processes must provide a
//! sound [`Program::possible_future`] alphabet excluding additional matching sends.
//! Its own future sends cannot supply it, because they follow it in program order.
//! Otherwise the answer is `Unknown`, not a guess about future sources. The alphabet
//! is used only for absence; all event windows and control dependencies come from
//! replaying actual guarded traces through `Program::next`.
//!
//! # What an impossibility certificate proves
//!
//! Every maximal semantic **forward** completion preserving the input graph is
//! impossible. It says nothing about a MUST backward revisit that changes that graph.
//! Do not use this certificate alone to delete an explorer subtree. It requires a
//! separate proof that its construction/revisit obligations are covered.
//!
//! The supported semantics are Asyn delivery, eager blocking receives, zero-time local
//! steps, and finite nondeterministic choices. Errors and nonblocking receives stop
//! lookahead. A feasible maximal deadlock is a completion, just as in MUST. As with the
//! explorer, the input must be a program-generated graph and `Program` must satisfy its
//! purity and sound-future contracts. Revalidation repeats all program/future queries;
//! it cannot prove that a user-supplied future alphabet is sound for arbitrary code.

use std::sync::Arc;

use crate::consistency::consistent;
use crate::event::{EventId, Label, Model, Tid, Val};
use crate::graph::ExecutionGraph;
use crate::program::{Program, ThreadNext};
use crate::scheduler::traces_of;

use super::{check, consistent_sources, Explanation, Schedule, TimedVerdict};

/// Limits the total work of one summary query, shared by all guarded alternatives.
/// Reaching either limit produces `Unknown`; it is never an impossibility proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LookaheadBudget {
    pub max_states: usize,
    /// Total events added to temporary graphs across all alternatives, not per branch.
    pub max_added_events: usize,
}

impl Default for LookaheadBudget {
    fn default() -> Self {
        Self {
            max_states: 128,
            max_added_events: 64,
        }
    }
}

/// Actual summary work. Solver work inside one `check` is not bounded by these limits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LookaheadStats {
    pub expanded_states: usize,
    pub added_events: usize,
    pub expanded_cases: usize,
    pub temporal_checks: usize,
}

/// A condition selecting one local continuation. A conjunction of these choices is
/// a path guard; alternative paths are disjoined, never merged into a single graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChoiceGuard {
    Receive { receive: EventId, source: EventId },
    Nondet { event: EventId, value: Val },
}

/// Why a thread cannot produce an additional source for a particular receive.
#[derive(Clone, Debug)]
pub enum SourceExclusion {
    /// It has no remaining program event under the guarded trace.
    Finished { tid: Tid },
    /// The supplied sound alphabet contains no send matching the receive. Windows
    /// in this alphabet are deliberately not used as temporal facts.
    FutureAlphabet {
        tid: Tid,
        trace: Vec<Option<Val>>,
        labels: Vec<Label>,
    },
    /// Sends after a receive on its own process would create a po/rf cycle.
    OwnProgramOrder { tid: Tid },
}

/// Evidence for one exhaustive case split in the summary tree.
#[derive(Clone, Debug)]
pub struct ChoiceCoverage {
    preceding_guard: Vec<ChoiceGuard>,
    event: EventId,
    alternatives: Vec<ChoiceGuard>,
    exclusions: Vec<SourceExclusion>,
}

impl ChoiceCoverage {
    pub fn preceding_guard(&self) -> &[ChoiceGuard] {
        &self.preceding_guard
    }
    pub fn event(&self) -> EventId {
        self.event
    }
    pub fn alternatives(&self) -> &[ChoiceGuard] {
        &self.alternatives
    }
    pub fn exclusions(&self) -> &[SourceExclusion] {
        &self.exclusions
    }
}

/// One rejected guarded case. The complete graph is retained so rechecking uses its
/// full disjunctive temporal system, not just the solver's diagnostic negative cycle.
#[derive(Clone, Debug)]
pub struct RejectedCase {
    guard: Vec<ChoiceGuard>,
    graph: ExecutionGraph,
    diagnostic: Explanation,
}

impl RejectedCase {
    pub fn guard(&self) -> &[ChoiceGuard] {
        &self.guard
    }
    pub fn graph(&self) -> &ExecutionGraph {
        &self.graph
    }
    /// Best-effort diagnostic, not a sufficient unsatisfiability proof by itself.
    pub fn diagnostic(&self) -> &Explanation {
        &self.diagnostic
    }
    pub fn recheck_timing(&self) -> bool {
        !check(&self.graph).is_feasible()
    }
}

/// An opaque proof result tied to the exact original graph commitments. All fields
/// are private: callers can inspect the evidence but cannot manufacture a certificate.
#[derive(Clone, Debug)]
pub struct ImpossibilityCertificate {
    base: ExecutionGraph,
    budget: LookaheadBudget,
    coverage: Vec<ChoiceCoverage>,
    cases: Vec<RejectedCase>,
    stats: LookaheadStats,
}

impl ImpossibilityCertificate {
    /// Checks exact graph support, including construction stamps and predicate object
    /// identity. This deliberately rejects even unrelated graph extensions or cuts.
    /// It does not establish that the program or its future summaries are unchanged.
    pub fn applies_to(&self, graph: &ExecutionGraph) -> bool {
        same_graph(&self.base, graph)
    }
    pub fn coverage(&self) -> &[ChoiceCoverage] {
        &self.coverage
    }
    pub fn cases(&self) -> &[RejectedCase] {
        &self.cases
    }
    pub fn stats(&self) -> LookaheadStats {
        self.stats
    }
    pub fn support(&self) -> &ExecutionGraph {
        &self.base
    }

    /// Rebuilds the guarded argument against the supplied program and future answers.
    /// A changed program, unknown future, or exhausted budget cannot validate a proof
    /// merely because its old negative-cycle diagnostic still looks plausible.
    pub fn revalidate<P: Program>(&self, graph: &ExecutionGraph, program: &P) -> bool {
        self.applies_to(graph)
            && matches!(
                check_completion(graph, program, self.budget),
                CompletionCheck::Impossible(_)
            )
    }
}

/// A complete maximal graph with one satisfying timestamp assignment. Clocks remain
/// existential witnesses; distinct schedules are not distinct graph-search results.
#[derive(Clone, Debug)]
pub struct CompletionWitness {
    graph: ExecutionGraph,
    schedule: Schedule,
    guard: Vec<ChoiceGuard>,
    stats: LookaheadStats,
}

impl CompletionWitness {
    pub fn terminal_graph(&self) -> &ExecutionGraph {
        &self.graph
    }
    pub fn schedule(&self) -> &Schedule {
        &self.schedule
    }
    pub fn guard(&self) -> &[ChoiceGuard] {
        &self.guard
    }
    pub fn stats(&self) -> LookaheadStats {
        self.stats
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnknownReason {
    BudgetExhausted,
    UnsupportedEvent {
        event: EventId,
    },
    /// No expandable receive has a proved complete source set.
    IncompleteSources {
        receives: Vec<EventId>,
    },
    InvalidInput,
    /// The first future label must be the actual next event, as required by Program.
    InvalidFutureHead {
        tid: Tid,
    },
}

/// An inconclusive result still reports work already spent inside lookahead.
#[derive(Clone, Debug)]
pub struct UnknownCompletion {
    reason: UnknownReason,
    stats: LookaheadStats,
}

impl UnknownCompletion {
    pub fn reason(&self) -> &UnknownReason {
        &self.reason
    }
    pub fn stats(&self) -> LookaheadStats {
        self.stats
    }
}

#[derive(Clone, Debug)]
pub enum CompletionCheck {
    Impossible(ImpossibilityCertificate),
    Witness(CompletionWitness),
    Unknown(UnknownCompletion),
}

impl CompletionCheck {
    pub fn stats(&self) -> LookaheadStats {
        match self {
            Self::Impossible(certificate) => certificate.stats(),
            Self::Witness(witness) => witness.stats(),
            Self::Unknown(unknown) => unknown.stats(),
        }
    }
}

/// Build a bounded, guarded future summary without changing `base` or using a main
/// scheduler policy. `Impossible` requires exhaustive coverage of every chosen source
/// or nondeterministic alternative; a single feasible partial case is only `Unknown`.
pub fn check_completion<P: Program>(
    base: &ExecutionGraph,
    program: &P,
    budget: LookaheadBudget,
) -> CompletionCheck {
    if budget.max_states == 0 || budget.max_added_events == 0 {
        return CompletionCheck::Unknown(UnknownCompletion {
            reason: UnknownReason::BudgetExhausted,
            stats: LookaheadStats::default(),
        });
    }
    if base.num_threads() > program.num_threads()
        || !consistent(base)
        || base.iter_events().any(|event| match base.label(event) {
            Label::Nondet { set } => base.nd_value(event).is_none_or(|v| !set.contains(v)),
            Label::Send { dst, .. } => *dst >= program.num_threads(),
            _ => false,
        })
    {
        return CompletionCheck::Unknown(UnknownCompletion {
            reason: UnknownReason::InvalidInput,
            stats: LookaheadStats::default(),
        });
    }
    let mut analysis = Analysis {
        program,
        budget,
        stats: LookaheadStats::default(),
    };
    match analysis.summarize(base.clone(), Vec::new()) {
        Summary::Impossible { coverage, cases } => {
            CompletionCheck::Impossible(ImpossibilityCertificate {
                base: base.clone(),
                budget,
                coverage,
                cases,
                stats: analysis.stats,
            })
        }
        Summary::Witness {
            graph,
            schedule,
            guard,
        } => CompletionCheck::Witness(CompletionWitness {
            graph,
            schedule,
            guard,
            stats: analysis.stats,
        }),
        Summary::Unknown(reason) => CompletionCheck::Unknown(UnknownCompletion {
            reason,
            stats: analysis.stats,
        }),
    }
}

enum Summary {
    Impossible {
        coverage: Vec<ChoiceCoverage>,
        cases: Vec<RejectedCase>,
    },
    Witness {
        graph: ExecutionGraph,
        schedule: Schedule,
        guard: Vec<ChoiceGuard>,
    },
    Unknown(UnknownReason),
}

struct Analysis<'a, P> {
    program: &'a P,
    budget: LookaheadBudget,
    stats: LookaheadStats,
}

impl<P: Program> Analysis<'_, P> {
    fn append(&mut self, graph: &mut ExecutionGraph, tid: Tid, label: Label) -> Option<EventId> {
        if self.stats.added_events >= self.budget.max_added_events {
            return None;
        }
        self.stats.added_events += 1;
        Some(graph.add_event(tid, label))
    }

    fn summarize(&mut self, mut graph: ExecutionGraph, guard: Vec<ChoiceGuard>) -> Summary {
        if self.stats.expanded_states >= self.budget.max_states {
            return Summary::Unknown(UnknownReason::BudgetExhausted);
        }
        self.stats.expanded_states += 1;
        if let Some(event) = graph.iter_events().find(|&e| !supported(graph.label(e))) {
            return Summary::Unknown(UnknownReason::UnsupportedEvent { event });
        }

        // One deterministic event at a time; this canonical drain is a restriction of
        // every completion, not a choice of physical delivery/consumption ordering.
        loop {
            self.stats.temporal_checks += 1;
            let schedule = match check(&graph) {
                TimedVerdict::Infeasible(diagnostic) => {
                    return Summary::Impossible {
                        coverage: Vec::new(),
                        cases: vec![RejectedCase {
                            guard,
                            graph,
                            diagnostic,
                        }],
                    }
                }
                TimedVerdict::Feasible(schedule) => schedule,
            };
            let traces = traces_of(&graph, self.program.num_threads());
            let next = self.program.next(&traces);
            if next.len() != self.program.num_threads() {
                return Summary::Unknown(UnknownReason::InvalidInput);
            }
            // Unsupported next events are not executed or guessed. Their other
            // threads' deterministic effects may still certify impossibility first.
            let deterministic = next.iter().enumerate().find_map(|(tid, step)| match step {
                ThreadNext::Next(
                    label @ Label::Send {
                        model: Model::Asyn,
                        dst,
                        ..
                    },
                ) if *dst < self.program.num_threads() => Some((tid, label.clone(), None)),
                ThreadNext::Next(label @ Label::Nondet { set }) if set.len() == 1 => {
                    Some((tid, label.clone(), Some(set[0])))
                }
                _ => None,
            });
            if let Some((tid, label, nd)) = deterministic {
                let Some(event) = self.append(&mut graph, tid, label) else {
                    return Summary::Unknown(UnknownReason::BudgetExhausted);
                };
                if let Some(value) = nd {
                    graph.set_nd(event, value);
                }
                continue;
            }
            if let Some((tid, _)) = next.iter().enumerate().find(|(_, step)| match step {
                ThreadNext::Next(label) => {
                    !supported(label)
                        || label
                            .dst()
                            .is_some_and(|dst| dst >= self.program.num_threads())
                }
                ThreadNext::Finished => false,
            }) {
                return Summary::Unknown(UnknownReason::UnsupportedEvent {
                    event: EventId::new(tid, graph.thread_len(tid)),
                });
            }

            // A finite nondeterministic choice is unconditionally exhaustive and
            // cannot be blocked by a different process. Expanding it first may also
            // reveal a future source hidden from an alphabet query at this frontier.
            if let Some((tid, label, set)) =
                next.iter().enumerate().find_map(|(tid, step)| match step {
                    ThreadNext::Next(label @ Label::Nondet { set }) => Some((tid, label, set)),
                    _ => None,
                })
            {
                let event = EventId::new(tid, graph.thread_len(tid));
                let alternatives = set
                    .iter()
                    .map(|&value| ChoiceGuard::Nondet { event, value })
                    .collect();
                return self.split(
                    graph,
                    guard,
                    label.clone(),
                    ChoiceCoverage {
                        preceding_guard: Vec::new(),
                        event,
                        alternatives,
                        exclusions: Vec::new(),
                    },
                );
            }

            let mut incomplete = Vec::new();
            for (tid, step) in next.iter().enumerate() {
                let ThreadNext::Next(label @ Label::Recv { blocking: true, .. }) = step else {
                    continue;
                };
                let sources = consistent_sources(&graph, tid, label);
                if sources.is_empty() {
                    continue;
                }
                let event = EventId::new(tid, graph.thread_len(tid));
                match complete_sources(self.program, &traces, &next, tid, label) {
                    Ok(Some(exclusions)) => {
                        let alternatives = sources
                            .into_iter()
                            .map(|source| ChoiceGuard::Receive {
                                receive: event,
                                source,
                            })
                            .collect();
                        return self.split(
                            graph,
                            guard,
                            label.clone(),
                            ChoiceCoverage {
                                preceding_guard: Vec::new(),
                                event,
                                alternatives,
                                exclusions,
                            },
                        );
                    }
                    Ok(None) => incomplete.push(event),
                    Err(reason) => return Summary::Unknown(reason),
                }
            }
            if !incomplete.is_empty() {
                return Summary::Unknown(UnknownReason::IncompleteSources {
                    receives: incomplete,
                });
            }
            // All remaining processes are finished or blocked with no currently
            // matching unread message. No future event can be produced at this cut.
            return Summary::Witness {
                graph,
                schedule,
                guard,
            };
        }
    }

    fn split(
        &mut self,
        graph: ExecutionGraph,
        guard: Vec<ChoiceGuard>,
        label: Label,
        mut coverage: ChoiceCoverage,
    ) -> Summary {
        coverage.preceding_guard = guard.clone();
        let mut children = Vec::new();
        let mut cases = Vec::new();
        let mut unknown = None;
        for choice in &coverage.alternatives {
            let mut child = graph.clone();
            let Some(event) = self.append(&mut child, coverage.event.tid, label.clone()) else {
                return Summary::Unknown(UnknownReason::BudgetExhausted);
            };
            match choice {
                ChoiceGuard::Receive { source, .. } => child.set_rf(event, Some(*source)),
                ChoiceGuard::Nondet { value, .. } => child.set_nd(event, *value),
            }
            self.stats.expanded_cases += 1;
            let mut child_guard = guard.clone();
            child_guard.push(choice.clone());
            match self.summarize(child, child_guard) {
                Summary::Impossible {
                    coverage,
                    cases: rejected,
                } => {
                    children.extend(coverage);
                    cases.extend(rejected);
                }
                witness @ Summary::Witness { .. } => return witness,
                Summary::Unknown(reason) => {
                    if unknown.is_none() {
                        unknown = Some(reason);
                    }
                }
            }
        }
        if let Some(reason) = unknown {
            return Summary::Unknown(reason);
        }
        children.insert(0, coverage);
        Summary::Impossible {
            coverage: children,
            cases,
        }
    }
}

fn supported(label: &Label) -> bool {
    matches!(
        label,
        Label::Send {
            model: Model::Asyn,
            ..
        } | Label::Recv { blocking: true, .. }
    ) || matches!(label, Label::Nondet { set } if !set.is_empty())
}

fn complete_sources<P: Program>(
    program: &P,
    traces: &[Vec<Option<Val>>],
    next: &[ThreadNext],
    receiver: Tid,
    label: &Label,
) -> Result<Option<Vec<SourceExclusion>>, UnknownReason> {
    let pred = label.pred().expect("called only for a blocking receive");
    let mut exclusions = Vec::with_capacity(next.len());
    for (tid, step) in next.iter().enumerate() {
        if tid == receiver {
            exclusions.push(SourceExclusion::OwnProgramOrder { tid });
        } else if step.is_finished() {
            exclusions.push(SourceExclusion::Finished { tid });
        } else {
            let Some(labels) = program.possible_future(tid, &traces[tid]) else {
                return Ok(None);
            };
            if labels.first() != step.label() {
                return Err(UnknownReason::InvalidFutureHead { tid });
            }
            if labels.iter().any(|label| match label {
                Label::Send { dst, val, .. } => *dst == receiver && pred.test_sym(*val),
                _ => false,
            }) {
                return Ok(None);
            }
            exclusions.push(SourceExclusion::FutureAlphabet {
                tid,
                trace: traces[tid].clone(),
                labels,
            });
        }
    }
    Ok(Some(exclusions))
}

fn same_graph(left: &ExecutionGraph, right: &ExecutionGraph) -> bool {
    left.num_threads() == right.num_threads()
        && (0..left.num_threads()).all(|tid| left.thread_len(tid) == right.thread_len(tid))
        && left.iter_events().all(|event| {
            left.stamp(event) == right.stamp(event)
                && left.label(event) == right.label(event)
                && match (left.label(event), right.label(event)) {
                    (Label::Recv { pred: a, .. }, Label::Recv { pred: b, .. }) => Arc::ptr_eq(a, b),
                    _ => true,
                }
                && left.reads_from(event) == right.reads_from(event)
                && left.nd_value(event) == right.nd_value(event)
        })
}
