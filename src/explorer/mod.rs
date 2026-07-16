//! The Must DPOR explorer (Algorithm 1).
//!
//! [`explore`] is the entry point: it walks every consistent execution graph starting
//! from the empty one. The backward-revisit half of the algorithm lives in [`revisit`].
//! Each recursive branch works on a clone of the graph, so no branch ever observes
//! another's edits.

mod execution;
mod parallel;
pub mod revisit;

pub use execution::{Execution, ExecutionKind};

use std::sync::Arc;

use crate::consistency::consistent;
use crate::event::{EventId, Label, Tid, Val};
use crate::graph::ExecutionGraph;
use crate::observer::Observer;
use crate::program::{Program, ThreadNext};
use crate::scheduler::{pick, traces_of, NextStep};

use parallel::Spawner;

/// Tunables for an `explore` run.
#[derive(Clone, Debug)]
pub struct Config {
    /// Thread priority permutation for `next_P`. `None` = the default `0..N`.
    pub priorities: Option<Vec<Tid>>,
    /// Stop the whole exploration at the first `error` event (line 5 of Algorithm 1
    /// says `exit`). Default `true`.
    ///
    /// When `false`, an error event finishes only its own thread and the branch keeps
    /// running, so every reachable error surfaces as its own erroneous terminal. This is
    /// sound: error-free programs are unaffected, because with no
    /// error event the terminal classification never runs the error scan, so full/blocked
    /// counts are identical to the `true` case.
    pub stop_on_error: bool,
    /// Optional cap on the number of terminal (full + blocked) executions; the run
    /// stops once it is reached. `None` = unbounded.
    pub max_executions: Option<usize>,
    /// Worker threads for the exploration. `1` (the default) runs the ordinary sequential
    /// search on the calling thread; `> 1` fans the independent subtrees out across that
    /// many workers. The set of executions is identical either way (only their order, and
    /// the best-effort nature of `max_executions` / `stop_on_error`, differ).
    pub threads: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            priorities: None,
            stop_on_error: true,
            max_executions: None,
            threads: 1,
        }
    }
}

impl Config {
    /// Run under an explicit priority permutation.
    pub fn with_priorities(mut self, priorities: Vec<Tid>) -> Self {
        self.priorities = Some(priorities);
        self
    }
    /// Keep exploring after an error instead of stopping.
    pub fn collect_errors(mut self) -> Self {
        self.stop_on_error = false;
        self
    }
    /// Explore across `threads` worker threads (clamped to at least one).
    pub fn with_threads(mut self, threads: usize) -> Self {
        self.threads = threads.max(1);
        self
    }
}

/// Verify a program, notifying `observer` throughout.
///
/// `make_program` builds a fresh program instance; it is called once for the sequential
/// run and once per worker for a parallel one (`Config::threads > 1`), so the process
/// runtime never has to cross a thread boundary. The single `observer` is shared by every
/// worker, hence the `Sync` bound - see [`observer`](crate::observer).
///
/// Nothing is returned: everything about the run reaches you through the observer (counts
/// via [`CountingObserver`](crate::CountingObserver), the executions themselves via
/// [`ExecutionCollector`](crate::observer::ExecutionCollector)).
pub fn explore<P, MK, O>(make_program: MK, observer: &O, config: Config)
where
    MK: Fn() -> P + Sync,
    P: Program,
    O: Observer + Sync,
{
    if config.threads > 1 {
        parallel::explore_parallel(make_program, observer, config);
        return;
    }

    let program = make_program();
    let n = program.num_threads();
    let priorities = config
        .priorities
        .clone()
        .unwrap_or_else(|| (0..n).collect());
    // Unconditional (not debug-only): a duplicate tid would silently drop executions in
    // release, and a tid >= N would panic on the priority index deep in `next_step`.
    assert!(
        is_permutation(&priorities, n),
        "verify: priorities {priorities:?} must be a permutation of 0..{n}"
    );

    let mut explorer = Explorer {
        program: &program,
        observer,
        priorities,
        stop_on_error: config.stop_on_error,
        max_executions: config.max_executions,
        terminal_count: 0,
        stop: false,
        fork: None,
    };
    explorer.visit(&ExecutionGraph::new());
}

fn is_permutation(p: &[Tid], n: usize) -> bool {
    if p.len() != n {
        return false;
    }
    let mut seen = vec![false; n];
    for &t in p {
        if t >= n || seen[t] {
            return false;
        }
        seen[t] = true;
    }
    true
}

/// Whether any thread of `g` ended in an `error`. An error event is always the last
/// event of its thread (it finishes the thread), so this only needs to check thread tails.
fn graph_has_error(g: &ExecutionGraph) -> bool {
    (0..g.num_threads()).any(|t| {
        let len = g.thread_len(t);
        len > 0 && g.label(EventId::new(t, len - 1)).is_error()
    })
}

/// Carries the shared state of one `explore` run down the recursion.
pub(crate) struct Explorer<'a, P: Program, O: Observer> {
    pub(crate) program: &'a P,
    pub(crate) observer: &'a O,
    pub(crate) priorities: Vec<Tid>,
    stop_on_error: bool,
    max_executions: Option<usize>,
    /// This worker's own full+blocked count, for the sequential `max_executions` cap.
    pub(crate) terminal_count: usize,
    /// Set once the run should unwind: an `exit`-on-error or the execution cap.
    pub(crate) stop: bool,
    /// `Some` under a parallel run: later sibling branches are shed to the shared work
    /// queue when another worker is idle, instead of being explored inline. `None` is the
    /// sequential path (see [`Explorer::branch`]).
    pub(crate) fork: Option<Arc<Spawner>>,
}

impl<P: Program, O: Observer> Explorer<'_, P, O> {
    /// `Visit_P(G)` (Algorithm 1, lines 2-14), building the per-thread `(traces, nexts)`
    /// state from scratch. `g` is consistent on entry (it arrived through
    /// `branch_if_consistent`, or is the empty graph). Used wherever the parent's state does
    /// not carry over: the root, a subtree taken from the work queue, and after a backward
    /// revisit restructures the graph.
    pub(crate) fn visit(&mut self, g: &ExecutionGraph) {
        if self.stopping() {
            return;
        }
        // `traces[i]` is thread `i`'s per-event trace, `nexts[i]` its next event under that
        // trace. Both are threaded down the recursion; adding an event mutates only the
        // acting thread's entry, so only that thread's next is recomputed.
        let mut traces = traces_of(g, self.program.num_threads());
        let mut nexts = self.program.next(&traces);
        self.visit_step(g, &mut traces, &mut nexts);
    }

    /// `Visit_P(G)` given the already-computed `(traces, nexts)`. Picks the next event from
    /// `nexts` (addability is still rechecked against `g`) and dispatches. The forward cases
    /// derive the child's state in place; error and the backward-revisit case rebuild it via
    /// [`visit`](Self::visit).
    fn visit_step(
        &mut self,
        g: &ExecutionGraph,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
    ) {
        if self.stopping() {
            return;
        }
        debug_assert!(
            *traces == traces_of(g, self.program.num_threads())
                && *nexts == self.program.next(traces),
            "threaded traces/nexts drifted from a fresh recompute"
        );
        match pick(g, nexts, &self.priorities) {
            // line 4: next_P(G) = nothing - a terminal execution.
            NextStep::Terminal { blocked } => {
                // In collect-errors mode a branch that ran through an error reaches its
                // terminal still carrying that error event, so it is an Error terminal, not
                // Full/Blocked.
                let kind = if !self.stop_on_error && graph_has_error(g) {
                    ExecutionKind::Error
                } else if blocked.is_empty() {
                    ExecutionKind::Full
                } else {
                    for &tid in &blocked {
                        self.observer.on_thread_blocked(g, tid);
                    }
                    ExecutionKind::Blocked
                };
                self.record(g.clone(), kind);
            }
            NextStep::Event { tid, label } => match &label {
                // line 5: error - see `visit_error`.
                Label::Error { .. } => self.visit_error(g, tid, label),
                // line 6: nondet - enumerate every value of the option set.
                Label::Nondet { .. } => self.visit_nondet(g, tid, label, traces, nexts),
                // line 7: receive - enumerate rf sources.
                Label::Recv { .. } => self.visit_recv(g, tid, label, traces, nexts),
                // lines 8-13: send - the no-revisit branch plus backward revisits.
                Label::Send { .. } => self.visit_send(g, tid, label, traces, nexts),
            },
        }
    }

    /// Append `entry` to thread `tid`'s trace, recompute just that thread's next event, run
    /// `body` with the updated `(traces, nexts)`, then restore both. `entry` is the value the
    /// new event contributes to its thread's trace: the value a receive read (`None` = ⊥), a
    /// nondet's chosen value, or `None` for a send/error.
    fn with_child_memo(
        &mut self,
        tid: Tid,
        entry: Option<Val>,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
        body: impl FnOnce(&mut Self, &mut Vec<Vec<Option<Val>>>, &mut Vec<ThreadNext>),
    ) {
        traces[tid].push(entry);
        let saved = std::mem::replace(&mut nexts[tid], self.program.next_thread(tid, &traces[tid]));
        body(self, traces, nexts);
        nexts[tid] = saved;
        traces[tid].pop();
    }

    /// Whether this branch should unwind now: a local stop (sequential `exit`/cap) or,
    /// in parallel mode, another worker having tripped the shared stop flag.
    pub(crate) fn stopping(&self) -> bool {
        self.stop
            || self
                .fork
                .as_ref()
                .is_some_and(|sp| sp.stop.load(std::sync::atomic::Ordering::Relaxed))
    }

    /// Set the stop flag, propagating to the shared flag so every worker unwinds.
    fn request_stop(&mut self) {
        self.stop = true;
        if let Some(sp) = &self.fork {
            sp.request_stop();
        }
    }

    /// Explore consistent child `g` as one branch of a node's sibling group. Sequentially
    /// (`fork == None`) this is just `visit(g)`. In parallel mode it is work-donating DFS:
    ///
    /// * the first branch of every node (`*first == true`) is always recursed inline, so a
    ///   worker keeps descending its own path;
    /// * later siblings are donated to the shared work queue when another worker is idle
    ///   ([`Spawner::wants_work`]); otherwise they too run inline.
    ///
    /// A worker thus never offloads its only path, yet sheds the next sibling whenever the
    /// queue drains.
    ///
    /// Correctness: `visit` is a pure function of `(g, program, priorities)` (stateless
    /// DPOR, no cross-branch state), so a child yields the same subtree of terminals
    /// whether explored inline or by another worker with an equivalent program. Each child
    /// is enqueued or recursed exactly once; the only shared effects are the notifications
    /// to the shared observer and the atomics (terminal count, stop flag).
    fn branch(&mut self, first: &mut bool, g: &ExecutionGraph) {
        if !*first {
            if let Some(sp) = &self.fork {
                if sp.wants_work() {
                    sp.push(g.clone());
                    return;
                }
            }
        }
        *first = false;
        self.visit(g);
    }

    /// [`branch`](Self::branch) carrying the parent's `(traces, nexts)`: a donated subtree
    /// recomputes from scratch on pop (only `g` is `Send`), while an inline child continues
    /// via [`visit_step`](Self::visit_step). Used by the forward cases.
    fn branch_memo(
        &mut self,
        first: &mut bool,
        g: &ExecutionGraph,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
    ) {
        if !*first {
            if let Some(sp) = &self.fork {
                if sp.wants_work() {
                    sp.push(g.clone());
                    return;
                }
            }
        }
        *first = false;
        self.visit_step(g, traces, nexts);
    }

    /// [`branch`](Self::branch) gated on consistency: if `g` is consistent, explore it as
    /// a sibling (carrying the `first` flag); otherwise report it inconsistent.
    fn branch_if_consistent(&mut self, first: &mut bool, g: &ExecutionGraph) {
        if self.stopping() {
            return;
        }
        if consistent(g) {
            self.branch(first, g);
        } else {
            self.observer.on_inconsistent(g);
        }
    }

    /// line 5: an `error` event.
    ///
    /// With `stop_on_error` (default) this is the paper's `exit`: record the erroneous
    /// graph and halt the whole search after the first error.
    ///
    /// Without it (`collect_errors`) the error finishes only its own thread and the branch
    /// keeps going, so other threads run to completion and any error they reach surfaces
    /// too. The erroneous graph is not recorded here - the branch records it at its
    /// terminal, where `graph_has_error` classifies it Error. Truncating the whole branch
    /// instead would hide errors reachable only after this one (`T0: assert(false) || T1:
    /// recv(); assert(...) || T2: send(1,...)` - T1's assert would never be explored).
    fn visit_error(&mut self, g: &ExecutionGraph, tid: Tid, label: Label) {
        let mut g2 = g.clone();
        let e = g2.add_event(tid, label);
        self.observer.on_event_added(&g2, e);
        if self.stop_on_error {
            self.record(g2, ExecutionKind::Error);
            self.request_stop();
        } else {
            // The error event is now in the trace, so this thread's `next` returns
            // Finished: the recursion cannot re-pick it and cannot run past it. A single
            // child, so it is always explored inline (never donated).
            self.visit(&g2);
        }
    }

    /// line 7: `for s in G.S union {bottom} do VisitIfConsistent(SetRF(G, e, s))`.
    ///
    /// No syntactic prefilter: every send plus bottom (the no-message source) is tried,
    /// and consistency does the filtering (a non-matching send, or bottom under a blocking
    /// receive, fails well-formedness). The bottom option is never dropped - it is the
    /// timeout of a non-blocking receive.
    fn visit_recv(
        &mut self,
        g: &ExecutionGraph,
        tid: Tid,
        label: Label,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
    ) {
        let mut base = g.clone();
        let e = base.add_event(tid, label);
        // Discipline (graph.rs): assign an rf immediately after adding a receive.
        base.set_rf(e, None);
        self.observer.on_event_added(&base, e);

        // Sources in a deterministic order: sends in (tid, idx) order, then bottom. The
        // enumeration order does not affect the set of explored executions (each rf source
        // is a distinct child, visited once), so the natural event order suffices.
        let mut sources: Vec<Option<EventId>> = base.iter_sends().map(Some).collect();
        sources.push(None); // bottom

        // `branch` never mutates the graph it is handed (it clones internally for its own
        // children, and once when donating to the queue), so one `base` is reused across
        // sources, re-pointing `e`'s rf in place for each.
        let mut first = true;
        for src in sources {
            if self.stopping() {
                return;
            }
            base.set_rf(e, src);
            self.observer.on_rf_choice(&base, e, src);
            // `e` is the freshly added maximal receive, so only clauses mentioning it can
            // break: the incremental `consistent_after_recv` suffices. Filter here, before
            // the `(traces, nexts)` update, so a rejected source costs no recompute.
            debug_assert_eq!(
                crate::consistency::consistent_after_recv(&base, e),
                consistent(&base),
                "incremental recv-consistency must agree with the full check"
            );
            if !crate::consistency::consistent_after_recv(&base, e) {
                self.observer.on_inconsistent(&base);
                continue;
            }
            // Trace entry for `e`: the value it read (`None` for a ⊥/timeout read).
            let entry = src.map(|s| base.label(s).payload().expect("send carries a payload"));
            self.with_child_memo(tid, entry, traces, nexts, |this, traces, nexts| {
                this.branch_memo(&mut first, &base, traces, nexts);
            });
        }
    }

    /// line 6: `case e in ND: for v in S do Visit_P(SetND(G, e, v))`.
    ///
    /// A nondet event enumerates every value of its finite option set. Each choice recurses
    /// through plain `Visit_P`, not `VisitIfConsistent`: a nondet value never participates
    /// in rf / well-formedness / the model predicates, so `g` being consistent on entry
    /// makes every `SetND` result consistent by construction.
    fn visit_nondet(
        &mut self,
        g: &ExecutionGraph,
        tid: Tid,
        label: Label,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
    ) {
        let mut g_add = g.clone();
        let e = g_add.add_event(tid, label);
        self.observer.on_event_added(&g_add, e);

        // `Label::nondet` canonicalised the set to sorted+unique, so this explores
        // min(S) first (the line-19 canonical value) and each value exactly once.
        let set = g_add
            .label(e)
            .nd_set()
            .expect("visit_nondet on a non-nondet label")
            .to_vec();
        // Reuse one `g_add` across all values (see `visit_recv`), re-pointing `e`'s nondet
        // choice in place.
        let mut first = true;
        for v in set {
            if self.stopping() {
                return;
            }
            g_add.set_nd(e, v);
            // A nondet event's trace entry is its chosen value.
            self.with_child_memo(tid, Some(v), traces, nexts, |this, traces, nexts| {
                this.branch_memo(&mut first, &g_add, traces, nexts);
            });
        }
    }

    /// lines 8-13: add the send, explore the no-revisit branch (line 9), then attempt every
    /// backward revisit (lines 10-13). The revisit loop runs on `g_add` regardless of
    /// whether line 9's graph was consistent - Algorithm 1 does not gate it, and a revisit
    /// can delete the very events that made `g_add` inconsistent.
    fn visit_send(
        &mut self,
        g: &ExecutionGraph,
        tid: Tid,
        label: Label,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
    ) {
        let mut g_add = g.clone();
        let e = g_add.add_event(tid, label);
        self.observer.on_event_added(&g_add, e);

        // The line-9 child and every backward-revisit child are siblings of this send
        // node, so they share one `first` flag (the first explored inline, the rest
        // donatable).
        let mut first = true;
        // line 9: `e` is simply added. A ≤_G-maximal *unread* send is consistent in every
        // model (it is so-after everything in its thread / has no porf-successors, so it
        // cannot be the `u` of clause (b), never appears in clause (c), and has no outgoing
        // edge in the mbox graph). So branch unconditionally rather than re-checking the
        // whole graph; the debug assertion guards the proof.
        if !self.stopping() {
            debug_assert!(
                consistent(&g_add),
                "line-9 maximal unread send must be consistent"
            );
            // A send contributes no read value to its thread's trace.
            self.with_child_memo(tid, None, traces, nexts, |this, traces, nexts| {
                this.branch_memo(&mut first, &g_add, traces, nexts);
            });
        }
        if self.stopping() {
            return;
        }
        // lines 10-13. A backward revisit restructures the graph, so its children take the
        // fresh `visit` path rather than a derived state.
        self.backward_revisits(&mut first, &g_add, e);
    }

    /// Record a terminal execution and honour the `max_executions` cap.
    fn record(&mut self, graph: ExecutionGraph, kind: ExecutionKind) {
        let exec = Execution::new(graph);
        self.observer.on_execution(&exec, kind);
        if matches!(kind, ExecutionKind::Full | ExecutionKind::Blocked) {
            self.terminal_count += 1;
        }
        if let Some(limit) = self.max_executions {
            let hit = if let Some(sp) = &self.fork {
                // Parallel: the cap is over the global terminal count (full + blocked),
                // tracked atomically. Best-effort - workers already in flight may overshoot
                // slightly before they observe the stop flag.
                matches!(kind, ExecutionKind::Full | ExecutionKind::Blocked)
                    && sp.record_terminal() >= limit
            } else {
                self.terminal_count >= limit
            };
            if hit {
                self.request_stop();
            }
        }
    }
}
