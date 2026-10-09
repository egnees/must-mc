//! The Must DPOR explorer (Algorithm 1).
//!
//! [`explore`] is the entry point: it walks every consistent execution graph starting
//! from the empty one. The backward-revisit half of the algorithm lives in [`revisit`].
//! Forward branches append in place and restore the exact parent on return.
//! Backward cuts, donated subtrees, and observer snapshots own independent graphs.

mod execution;
pub mod frozen;
pub mod ownership;
mod parallel;
pub mod receive_tail;
mod repair_owner;
pub mod revisit;
pub mod source_order;

pub use execution::{Execution, ExecutionKind};
pub use source_order::SourceOrder;

use std::sync::Arc;

use crate::consistency::consistent;
use crate::event::{EventId, Label, Tid, Val};
use crate::graph::ExecutionGraph;
use crate::observer::Observer;
use crate::program::replay_cache::CachedProgram;
use crate::program::{Program, ProgramCursor, ThreadNext};
use crate::scheduler::{pick_with_read_marks, pooled_traces_of, traces_of, NextStep};

use parallel::Spawner;

thread_local! {
    static UNREAD_POOL: std::cell::RefCell<Vec<Vec<usize>>> =
        const { std::cell::RefCell::new(Vec::new()) };
    static UNREAD_SOURCE_POOL: std::cell::RefCell<Vec<Vec<Vec<EventId>>>> =
        const { std::cell::RefCell::new(Vec::new()) };
    static CURSOR_POOL: std::cell::RefCell<Vec<Vec<Option<ProgramCursor>>>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Committed forward RF state. Each worker rebuilds it for a root or backward
/// cut; append/pop branches update it together with the graph and local traces.
/// Destinations outside the program have no scheduled receiver and need no slot.
struct ForwardReads {
    marks: crate::graph::PooledMarks,
    unread: Vec<usize>,
    /// Ordered unread sends per destination, maintained only for observers that
    /// explicitly permit omitting structurally rejected RF trials.
    sources: Option<Vec<Vec<EventId>>>,
    /// Continuations paired with this root's local traces/nexts. Unsupported
    /// programs allocate no sidecar; cuts and donated roots rebuild from None.
    cursors: Option<Vec<Option<ProgramCursor>>>,
}

impl ForwardReads {
    fn new(g: &ExecutionGraph, threads: usize, index_sources: bool) -> Self {
        let mut marks = crate::graph::PooledMarks::take();
        crate::consistency::mark_read_sources(g, None, &mut marks);
        let mut unread = UNREAD_POOL.with(|pool| pool.borrow_mut().pop().unwrap_or_default());
        unread.clear();
        unread.resize(threads, 0);
        let mut sources = index_sources.then(|| {
            let mut rows =
                UNREAD_SOURCE_POOL.with(|pool| pool.borrow_mut().pop().unwrap_or_default());
            for row in &mut rows {
                row.clear();
            }
            rows.resize_with(threads, Vec::new);
            rows
        });
        for send in g.iter_sends() {
            if !marks.contains(send) {
                if let Some(dst) = g.label(send).dst().filter(|&dst| dst < threads) {
                    unread[dst] += 1;
                    if let Some(rows) = &mut sources {
                        // iter_sends already yields the exact source tiebreaker order.
                        rows[dst].push(send);
                    }
                }
            }
        }
        Self {
            marks,
            unread,
            sources,
            cursors: None,
        }
    }

    fn cursor(&self, tid: Tid) -> Option<ProgramCursor> {
        self.cursors.as_ref().and_then(|cursors| cursors[tid])
    }

    fn set_cursor(&mut self, tid: Tid, cursor: Option<ProgramCursor>) {
        if cursor.is_none() && self.cursors.is_none() {
            return;
        }
        let threads = self.unread.len();
        let cursors = self.cursors.get_or_insert_with(|| {
            let mut cursors = CURSOR_POOL.with(|pool| pool.borrow_mut().pop().unwrap_or_default());
            cursors.clear();
            cursors.resize(threads, None);
            cursors
        });
        cursors[tid] = cursor;
    }

    fn send_added(&mut self, g: &ExecutionGraph, send: EventId) {
        self.marks.grow(g);
        if let Some(dst) = g.label(send).dst().filter(|&dst| dst < self.unread.len()) {
            self.unread[dst] += 1;
            if let Some(rows) = &mut self.sources {
                let row = &mut rows[dst];
                let position = row
                    .binary_search(&send)
                    .expect_err("a fresh send cannot already be indexed");
                row.insert(position, send);
            }
        }
    }

    fn send_removed(&mut self, g: &ExecutionGraph, send: EventId) {
        debug_assert!(!self.marks.contains(send));
        if let Some(dst) = g.label(send).dst().filter(|&dst| dst < self.unread.len()) {
            self.unread[dst] -= 1;
            if let Some(rows) = &mut self.sources {
                let row = &mut rows[dst];
                let position = row
                    .binary_search(&send)
                    .expect("the removed unread send must be indexed");
                row.remove(position);
            }
        }
    }

    fn consume(&mut self, receiver: Tid, source: EventId) {
        let fresh = self.marks.insert(source);
        debug_assert!(fresh, "a consistent receive must consume an unread send");
        self.unread[receiver] -= 1;
        if let Some(rows) = &mut self.sources {
            let row = &mut rows[receiver];
            let position = row
                .binary_search(&source)
                .expect("an unread source must be indexed");
            row.remove(position);
        }
    }

    fn restore_consume(&mut self, receiver: Tid, source: EventId) {
        let removed = self.marks.remove(source);
        debug_assert!(removed, "nested visits must restore committed RF marks");
        self.unread[receiver] += 1;
        if let Some(rows) = &mut self.sources {
            let row = &mut rows[receiver];
            let position = row
                .binary_search(&source)
                .expect_err("a consumed source must not be indexed");
            row.insert(position, source);
        }
    }

    fn matches_graph(&self, g: &ExecutionGraph) -> bool {
        g.iter_sends()
            .all(|send| self.marks.contains(send) == g.is_read(send))
            && self.unread.iter().enumerate().all(|(tid, &count)| {
                count
                    == g.iter_sends()
                        .filter(|&send| g.label(send).dst() == Some(tid) && !g.is_read(send))
                        .count()
            })
            && self.sources.as_ref().is_none_or(|rows| {
                rows.iter().enumerate().all(|(tid, sources)| {
                    *sources
                        == g.iter_sends()
                            .filter(|&send| g.label(send).dst() == Some(tid) && !g.is_read(send))
                            .collect::<Vec<_>>()
                })
            })
    }
}

impl std::ops::Deref for ForwardReads {
    type Target = crate::graph::Marks;
    fn deref(&self) -> &Self::Target {
        &self.marks
    }
}

impl Drop for ForwardReads {
    fn drop(&mut self) {
        UNREAD_POOL.with(|pool| {
            let mut pool = pool.borrow_mut();
            if pool.len() < 32 {
                pool.push(std::mem::take(&mut self.unread));
            }
        });
        if let Some(rows) = self.sources.take() {
            // Bound retained buffers independently of the model's thread count.
            if rows.capacity() <= 256 && rows.iter().map(Vec::capacity).sum::<usize>() <= 4096 {
                let _ = UNREAD_SOURCE_POOL.try_with(|pool| {
                    let mut pool = pool.borrow_mut();
                    if pool.len() < 32 {
                        pool.push(rows);
                    }
                });
            }
        }
        if let Some(cursors) = self.cursors.take() {
            if cursors.capacity() <= 256 {
                let _ = CURSOR_POOL.try_with(|pool| {
                    let mut pool = pool.borrow_mut();
                    if pool.len() < 32 {
                        pool.push(cursors);
                    }
                });
            }
        }
    }
}

#[cfg(test)]
mod forward_read_tests {
    use super::*;
    use crate::event::{Model, Pred};

    #[test]
    fn committed_counters_restore_across_nested_forward_branches_and_reused_ids() {
        let mut g = ExecutionGraph::new();
        let old = g.add_event(0, Label::send(Model::Asyn, 1, "old"));
        let held = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(held, Some(old));
        g.add_event(0, Label::send(Model::Asyn, 99, "outside"));
        let mut read = ForwardReads::new(&g, 3, true);
        assert_eq!(read.unread, [0, 0, 0]);
        assert!(read.matches_graph(&g));

        let send_checkpoint = g.checkpoint();
        let source = g.add_event(2, Label::send(Model::Asyn, 1, "new"));
        read.send_added(&g, source);
        assert_eq!(read.unread, [0, 1, 0]);
        assert!(read.matches_graph(&g));
        let retained = g.clone();

        let recv_checkpoint = g.checkpoint();
        let receive = g.add_event(1, Label::recv_nb(Pred::any()));
        g.set_rf_forward(receive, Some(source));
        read.consume(1, source);
        assert_eq!(read.unread, [0, 0, 0]);
        assert!(read.matches_graph(&g));
        read.restore_consume(1, source);
        g.set_rf_forward(receive, None);
        assert!(read.matches_graph(&g));
        g.restore_append(recv_checkpoint, receive);
        read.send_removed(&g, source);
        g.restore_append(send_checkpoint, source);
        assert_eq!(read.unread, [0, 0, 0]);
        assert!(read.matches_graph(&g));

        let sibling_checkpoint = g.checkpoint();
        let sibling = g.add_event(2, Label::send(Model::Asyn, 0, "sibling"));
        assert_eq!(sibling, source);
        read.send_added(&g, sibling);
        assert_eq!(read.unread, [1, 0, 0]);
        assert!(read.matches_graph(&g));
        read.send_removed(&g, sibling);
        g.restore_append(sibling_checkpoint, sibling);
        assert!(read.matches_graph(&g));
        assert_eq!(ForwardReads::new(&retained, 3, true).unread, [0, 1, 0]);
    }

    #[test]
    fn backward_cut_rebuilds_counts_when_a_receive_disappears() {
        let mut g = ExecutionGraph::new();
        let source = g.add_event(0, Label::send(Model::Asyn, 1, "message"));
        let receive = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(receive, Some(source));
        let parent = ForwardReads::new(&g, 2, true);
        assert_eq!(parent.unread, [0, 0]);
        let keep = [source].into_iter().collect();
        let cut = g.restrict(&keep);
        let rebuilt = ForwardReads::new(&cut, 2, true);
        assert_eq!(rebuilt.unread, [0, 1]);
        assert!(rebuilt.matches_graph(&cut));
        assert!(parent.matches_graph(&g));
    }

    #[test]
    fn source_index_stays_ordered_across_long_nested_branches_and_rebuilds() {
        let mut g = ExecutionGraph::new();
        for position in 0..81 {
            let sender = [2, 0, 1][position % 3];
            let destination = if position % 7 == 0 {
                99
            } else {
                3 + position % 2
            };
            let model = [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox][position % 4];
            g.add_event(sender, Label::send(model, destination, "message"));
        }
        let original = g.clone();
        let mut read = ForwardReads::new(&g, 5, true);
        assert!(read.matches_graph(&g));
        assert!(read.sources.as_ref().unwrap()[3].len() > 32);
        let sources = read.sources.as_ref().unwrap()[3].clone();
        let mut undo = Vec::new();
        for source in sources.into_iter().rev() {
            let checkpoint = g.checkpoint();
            let receive = g.add_event(3, Label::recv_nb(Pred::any()));
            g.set_rf_forward(receive, Some(source));
            read.consume(3, source);
            assert!(read.matches_graph(&g));
            undo.push((checkpoint, receive, source));
        }
        assert!(read.sources.as_ref().unwrap()[3].is_empty());
        for (checkpoint, receive, source) in undo.into_iter().rev() {
            read.restore_consume(3, source);
            g.set_rf_forward(receive, None);
            g.restore_append(checkpoint, receive);
            assert!(read.matches_graph(&g));
        }
        assert_eq!(g.canonical_key(), original.canonical_key());
        let checkpoint = g.checkpoint();
        let send = g.add_event(0, Label::send(Model::Asyn, 3, "new"));
        read.send_added(&g, send);
        assert!(read.matches_graph(&g));
        read.send_removed(&g, send);
        g.restore_append(checkpoint, send);
        assert!(read.matches_graph(&g));
        let cut = g.restrict_to_lens(&[12, 20, 7, 0]);
        assert!(ForwardReads::new(&cut, 5, true).matches_graph(&cut));
        let unindexed = ForwardReads::new(&original, 5, false);
        assert!(unindexed.sources.is_none());
        assert!(unindexed.matches_graph(&original));
    }
}

/// Limits for temporal certificates. A zero limit disables all certificate layers.
/// Frozen-core extraction and its consistency trials are not bounded by `max_states`.
/// A partially drained mandatory graph can still certify impossibility.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertifiedTimeConfig {
    /// Maximum states in each legacy semantic/coverage walk, excluding core extraction.
    pub max_states: usize,
    /// Maximum mandatory additions per frozen-core check; also bounds each legacy walk.
    pub max_added_events: usize,
}

impl Default for CertifiedTimeConfig {
    fn default() -> Self {
        Self {
            max_states: 128,
            max_added_events: 64,
        }
    }
}

/// Tunables for an `explore` run.
#[derive(Clone, Debug)]
pub struct Config {
    /// Thread priority permutation for `next_P`. `None` = the default `0..N`.
    pub priorities: Option<Vec<Tid>>,
    /// Stable total source order for untimed canonical completion. Incompatible with T2.
    pub source_order: SourceOrder,
    /// Stop the whole exploration at the first `error` event (line 5 of Algorithm 1
    /// says `exit`). Default `true`.
    ///
    /// When `false`, an error event finishes only its own thread and the branch keeps
    /// running, so every reachable error surfaces as its own erroneous terminal. This is
    /// sound: error-free programs are unaffected, because with no
    /// error event the terminal classification never runs the error scan, so full/blocked
    /// counts are identical to the `true` case.
    pub stop_on_error: bool,
    /// Stop after reporting the first accepted Error terminal, after timing verification.
    /// Unlike `stop_on_error`, error prefixes remain explorable until a terminal is
    /// reached. Filtered errors, Full and Blocked terminals do not trigger this flag.
    /// Default false. Use [`with_stop_on_terminal_error`](Self::with_stop_on_terminal_error)
    /// to also disable immediate error-prefix stopping. In parallel this is best-effort:
    /// workers already reporting terminals may produce additional outcomes.
    pub stop_on_terminal_error: bool,
    /// Optional cap on the number of terminal (full + blocked) executions; the run
    /// stops once it is reached. `None` = unbounded.
    ///
    /// A terminal suppressed by [`time_filter`](Self::time_filter) is *not* an execution of
    /// the timed program, so it counts towards neither this cap nor the terminal count.
    pub max_executions: Option<usize>,
    /// Optional construction budget: maximum sends in the current graph, across all
    /// threads (including already consumed sends). `None` = unbounded.
    ///
    /// Before adding a send beyond this budget, abandon that subtree and notify
    /// [`Observer::on_send_limit`]. This is an
    /// inconclusive cutoff, NOT a terminal execution or a protocol error. Receives
    /// and other events may still run at exactly the limit.
    ///
    /// This is a resource bound, not complete bounded model checking: a backward
    /// revisit may need an over-budget intermediate graph to discover a smaller
    /// execution. If any cutoff occurs, absence of errors proves nothing about
    /// unexplored executions, even those with at most this many sends. It also
    /// does not bound loops that make progress without sending, or temporary
    /// graphs built by internal consistency and timing lookahead.
    pub max_sends: Option<usize>,
    /// Optional property-directed omission of certified receive-only suffixes.
    /// Disabled by default, preserving graph enumeration and paper oracle counts.
    /// Only untimed Asyn is eligible, and all observers must explicitly accept a
    /// proved family. Omitted families are reported separately from terminals.
    pub receive_tail: Option<receive_tail::ReceiveTailBudget>,
    /// Worker threads for the exploration. `1` (the default) runs the ordinary sequential
    /// search on the calling thread; `> 1` fans the independent subtrees out across that
    /// many workers. The set of executions is identical either way (only their order, and
    /// the best-effort nature of `max_executions` / `stop_on_error`, differ).
    pub threads: usize,
    /// Suppress terminals that are not eager-time-realizable (the time-intervals extension,
    /// engine_plan §3). When `true`, a terminal graph consistent in the untimed sense but
    /// with no schedule satisfying the eager receive semantics
    /// ([`crate::time::eager_feasible`]) is routed to
    /// [`Observer::on_execution_filtered`] instead of
    /// `on_execution`, and counts towards neither the terminal count nor `max_executions`.
    /// Default `false` (every untimed oracle count is unchanged).
    ///
    /// Requires [`collect_errors`](Self::collect_errors) or
    /// [`with_stop_on_terminal_error`](Self::with_stop_on_terminal_error):
    /// `time_filter` with `stop_on_error`
    /// is unsupported and panics, because an eager-infeasible *error* prefix must stay
    /// explorable — a consistent, time-realizable terminal can be reachable only by a
    /// backward revisit *out of* that error graph (revisit completeness, engine_plan §3 B1).
    pub time_filter: bool,
    /// Use direct mailbox delivery and timed timeout/poll completion clocks.
    /// Supports Asyn, P2p and Mbox sends; abstract nonblocking receives and Cd
    /// are rejected. Requires terminal filtering and original MUST canonicity.
    /// This explicit flag also applies to prefixes without a timed receive.
    pub mailbox_time: bool,
    /// Enable experimental **eager-time predicate** exploration (T2; see `T2_PLAN.md`).
    /// Unlike [`time_filter`](Self::time_filter), this applies four coupled changes during
    /// construction. General completeness is false: a forward gate can discard the
    /// construction of a later repairing send, even with exact future summaries.
    /// The constructive owner check repairs some duplicates but does not establish
    /// general completeness or uniqueness. Use original MUST plus terminal verification
    /// as the reference.
    ///
    /// * **T-DES** ([`crate::scheduler::pick`]): a discrete-event scheduling order by lower-bound
    ///   time, replacing the priority order and determining insertion order `≤_G`;
    /// * **T-PRED** (`Explorer::visit_recv`): an rf-fork is taken only when the resulting
    ///   prefix is eager-time-feasible (`time::check(..).is_feasible()`), not merely consistent;
    /// * **T-CANON** ([`crate::explorer::revisit::get_cons_tiebreaker`]): the canonical source of
    ///   a blocking receive is the earliest-arriving one (`avail`-LB), not the `(tid,idx)`-min;
    /// * **T-GATE** (`Explorer::visit_send` line 9, [`crate::explorer::revisit`] line 13): a
    ///   forward send / backward revisit is gated on `time::forced_closure_feasible`, which
    ///   rejects a child whose *obligatory* continuation is eager-infeasible (the refuted-L3
    ///   replacement).
    ///
    /// Like [`time_filter`](Self::time_filter) it requires [`collect_errors`](Self::collect_errors)
    /// (same revisit-completeness reason) and is **mutually exclusive** with it (they are two
    /// different regimes for the same extension); `explore` panics on either violation. Default
    /// `false`; with the flag off, every count is byte-identical to the untimed explorer.
    pub time_predicate: bool,
    /// **Diagnostic ladder level** of the predicate regime (`C1_HARDENING_SPEC` §D.4): which of
    /// T2's pruners are switched on. Read *only* when [`time_predicate`](Self::time_predicate)
    /// is set; ignored otherwise.
    ///
    /// | level | T-DES | T-CANON + PASS oracle | T-PRED (line 7) | T-GATE (lines 9/13) | terminals |
    /// |---|---|---|---|---|---|
    /// | 1 | ✓ | — (untimed canon) | — | — | post-filter — this is [`time_zombie`](Self::time_zombie), *not* this field |
    /// | 2 | ✓ | ✓ | — | — | post-filter |
    /// | 3 | ✓ | ✓ | ✓ | — | post-filter |
    /// | 4 | ✓ | ✓ | ✓ | ✓ | none needed (feasible by construction) |
    ///
    /// Levels 2 and 3 still record only *eager-realizable* terminals — they route the rest to
    /// [`Observer::on_execution_filtered`] exactly as
    /// [`time_filter`](Self::time_filter)/[`time_zombie`](Self::time_zombie) do — because without
    /// T-PRED/T-GATE the walk reaches graphs no schedule realizes. At level 4 that filter should
    /// be vacuous, and a debug build asserts that it is; it is applied all the same, so that a
    /// broken invariant costs a missing execution rather than a *reported* one no schedule
    /// realizes.
    ///
    /// The point of the ladder is *localisation*, not a shipping mode: diffing the realizable key
    /// sets of two adjacent levels pins any completeness loss on exactly one mechanism (see
    /// `tests/ladder.rs`). Default `4` — i.e. plain [`with_time_predicate`](Self::with_time_predicate)
    /// is byte-for-byte the level-4 configuration and nothing about the shipping regime changes.
    pub time_predicate_level: u8,
    /// **T2⁰ / the `L2′` rung** (`T2_COMPLETENESS_VI_2` §0.1 Т-RED′, recipe VI-1 §8 R-7): force
    /// lines **18, 19 and 22** of `RevisitCondition` — all three *canon* arms (non-blocking
    /// receive, nondet value, blocking-receive source) — to `true`, leaving everything else
    /// (T-DES, T-PRED, both T-GATEs, and arm 21, which carries termination) as configured.
    ///
    /// Arm 18 is in that list and **must** be: once `pass_nb` made it an existential rule rather
    /// than the structural "reads ⊥", an active arm 18 can reject a revisit that zombie performs,
    /// so T2⁰ stops majorising the zombie tree. Т-RED as originally stated over {19, 22} is
    /// refuted for exactly that reason; Т-RED′ over {18, 19, 22} is the proved form (the VI-1
    /// §3.1 proof transfers verbatim — no step used arm 18's structurality, it was simply not
    /// listed).
    ///
    /// Т-RED′ proves that the resulting tree is the zombie tree plus extra revisits minus exactly
    /// the subtrees T-PRED and the two gates cut. Completeness of T2⁰ is therefore *equivalent* to
    /// global C1 alone, with the canon factored out — which turns
    /// `realizable(T2) ⊆ realizable(T2⁰) ⊆ realizable(zombie)` into the cheapest possible machine
    /// disjunction: a strict `⊊` on the left blames the canon (arms 18/19/22), a strict `⊊` on the
    /// right blames the pruning (global C1).
    ///
    /// It is a *diagnostic*, never a shipping regime: `true` is weaker than any canon rule, so the
    /// same graph is reached by many paths and duplicates are expected (optimality-(a) is given up
    /// on purpose; completeness and termination are not affected — `RevisitCondition` is a
    /// duplicate-elimination device, not a termination device). Default `false`.
    pub time_canon_free: bool,
    /// The **zombie** regime of the time extension (T2_ORACLE_SPEC Part 2): the untimed
    /// Algorithm 1 — untimed canon, no T-PRED, no T-GATE — run under the *DES insertion order*
    /// ([`crate::scheduler::pick`] with the des bit set) with the post-hoc realizability filter
    /// on terminals (exactly [`time_filter`](Self::time_filter)'s `record` routing).
    ///
    /// Correct by construction: Theorem 4.1 holds verbatim for any deterministic `next_P`
    /// policy, and the terminal filter is the proven T1 lemma. Against T1 it prunes *nothing* —
    /// it differs only in `≤_G` (DES order instead of priority order). Its role:
    /// 1. isolate `pick_des` as a valid `next_P` (zombie counts == T1-filter counts is a test of
    ///    the policy alone, decoupled from the T2 machinery);
    /// 2. arbitration under the same `≤_G`: zombie's canonical sources/stamps are directly
    ///    comparable with the oracle-T2 run on forward segments;
    /// 3. the fallback if the T2 oracle is intractable.
    ///
    /// Requires [`collect_errors`](Self::collect_errors) (same revisit-completeness reason as
    /// `time_filter`) and is mutually exclusive with both `time_filter` and `time_predicate`;
    /// `explore` panics on a violation. Default `false`.
    pub time_zombie: bool,
    /// Prune using immutable causal cores and mandatory deterministic continuations,
    /// with an additional bounded semantic/coverage fallback for Asyn programs.
    /// Requires `time_filter` or `time_zombie`, `collect_errors`, and untimed canonicity
    /// (`time_predicate` and `time_canon_free` false).
    ///
    /// Legacy timing requires the WHOLE program, including future sends, to use
    /// Asyn/P2p channels. With `mailbox_time`, Asyn/P2p/Mbox are supported using
    /// portable immutable anchors and first-alteration supports; the older bounded
    /// semantic/coverage fallback is disabled. Unknown retains the subtree.
    /// This rule need not reject every infeasible subtree; timestamps are not graph identity.
    pub certified_time: Option<CertifiedTimeConfig>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            priorities: None,
            source_order: SourceOrder::default(),
            stop_on_error: true,
            stop_on_terminal_error: false,
            max_executions: None,
            max_sends: None,
            receive_tail: None,
            threads: 1,
            time_filter: false,
            mailbox_time: false,
            time_predicate: false,
            time_predicate_level: 4,
            time_canon_free: false,
            time_zombie: false,
            certified_time: None,
        }
    }
}

impl Config {
    /// Run under an explicit priority permutation.
    pub fn with_priorities(mut self, priorities: Vec<Tid>) -> Self {
        self.priorities = Some(priorities);
        self
    }
    /// Set the total source order without filtering any untimed-consistent candidates.
    /// The default is original EventId order; self-send preference can strengthen
    /// immutable-core certificates for protocols whose timers are self-messages.
    pub fn with_source_order(mut self, order: SourceOrder) -> Self {
        self.source_order = order;
        self
    }
    /// Keep exploring after an error instead of stopping.
    pub fn collect_errors(mut self) -> Self {
        self.stop_on_error = false;
        self.stop_on_terminal_error = false;
        self
    }
    /// Stop on the first accepted Error terminal, keeping error prefixes explorable.
    /// Compatible with terminal timing filters and certified pruning. The observer
    /// receives the counterexample before stopping; time-infeasible errors do not stop
    /// the search. Full and Blocked terminals do not stop it either.
    pub fn with_stop_on_terminal_error(mut self) -> Self {
        self.stop_on_error = false;
        self.stop_on_terminal_error = true;
        self
    }
    /// Limit sends across all threads of a construction graph. Any cutoff makes
    /// the search incomplete; see [`max_sends`](Self::max_sends).
    pub fn with_max_sends(mut self, max_sends: usize) -> Self {
        self.max_sends = Some(max_sends);
        self
    }
    /// Enable bounded receive-tail proofs for an explicitly accepting observer.
    pub fn with_receive_tail(mut self, budget: receive_tail::ReceiveTailBudget) -> Self {
        self.receive_tail = Some(budget);
        self
    }
    /// Explore across `threads` worker threads (clamped to at least one).
    pub fn with_threads(mut self, threads: usize) -> Self {
        self.threads = threads.max(1);
        self
    }
    /// Enable the eager-time realizability filter (see [`time_filter`](Self::time_filter)).
    /// Combine with [`collect_errors`](Self::collect_errors) or
    /// [`with_stop_on_terminal_error`](Self::with_stop_on_terminal_error), or `explore` panics.
    pub fn with_time_filter(mut self) -> Self {
        self.time_filter = true;
        self
    }
    /// Select the timed mailbox semantics described in `docs/P2P_AND_TIMED_RECEIVES.md`.
    /// Combine with `collect_errors()` or `with_stop_on_terminal_error()`, and
    /// `with_time_filter()`, `with_time_zombie()`
    /// or `with_certified_time()`. This selects semantics independently of pruning.
    pub fn with_mailbox_time(mut self) -> Self {
        self.mailbox_time = true;
        self
    }
    /// Enable the full eager-time predicate exploration (see
    /// [`time_predicate`](Self::time_predicate)). Must be combined with
    /// [`collect_errors`](Self::collect_errors) and must **not** be combined with
    /// [`with_time_filter`](Self::with_time_filter), or `explore` panics.
    pub fn with_time_predicate(mut self) -> Self {
        self.time_predicate = true;
        self
    }
    /// One rung of the **diagnostic ladder** (`C1_HARDENING_SPEC` §D.4): the predicate regime with
    /// T2's pruners switched on one at a time — see
    /// [`time_predicate_level`](Self::time_predicate_level) for the table.
    ///
    /// * `1` — delegates to [`with_time_zombie`](Self::with_time_zombie) (it *is* the L1 row:
    ///   T-DES + untimed canon + no T-PRED/T-GATE + the terminal post-filter), so the validated
    ///   correct-by-construction reference is reused rather than re-implemented;
    /// * `2..=4` — the predicate regime at that level; `4` is exactly
    ///   [`with_time_predicate`](Self::with_time_predicate).
    ///
    /// Panics on `l == 0` or `l > 4`. Carries the same `collect_errors` / mutual-exclusion
    /// requirements as the regime it selects.
    pub fn with_time_predicate_level(self, l: u8) -> Self {
        assert!(
            (1..=4).contains(&l),
            "with_time_predicate_level: level {l} is outside 1..=4"
        );
        if l == 1 {
            return self.with_time_zombie();
        }
        let mut cfg = self.with_time_predicate();
        cfg.time_predicate_level = l;
        cfg
    }
    /// Force all three canon arms (18, 19, 22) of `RevisitCondition` to `true` (see
    /// [`time_canon_free`](Self::time_canon_free)). Combined with
    /// [`with_time_predicate_level(4)`](Self::with_time_predicate_level) this is the **`L2′` rung**
    /// = Т-RED′'s `T2⁰` (`T2_COMPLETENESS_VI_2` §0.1).
    pub fn with_canon_free(mut self) -> Self {
        self.time_canon_free = true;
        self
    }
    /// Enable the zombie regime (see [`time_zombie`](Self::time_zombie)): untimed Algorithm 1
    /// under the DES insertion order with the post-hoc terminal filter. Must be combined with
    /// [`collect_errors`](Self::collect_errors) and must **not** be combined with
    /// [`with_time_filter`](Self::with_time_filter) or
    /// [`with_time_predicate`](Self::with_time_predicate), or `explore` panics.
    pub fn with_time_zombie(mut self) -> Self {
        self.time_zombie = true;
        self
    }

    /// Enable certificate pruning with untimed MUST canonicity. Uses DES unless
    /// `with_time_filter()` already selected the priority policy. Requires
    /// `collect_errors()` and a whole program using only Asyn/P2p sends; see
    /// [`certified_time`](Self::certified_time) for the semantic scope.
    pub fn with_certified_time(mut self) -> Self {
        self.certified_time.get_or_insert_with(Default::default);
        if !self.time_filter {
            self.time_zombie = true;
        }
        self
    }

    /// Set certificate budgets. A zero limit disables all checks and callbacks,
    /// preserving the construction for the selected source order. Nonzero limits
    /// bound proof continuations, not immutable-core extraction or solver complexity.
    pub fn with_certified_time_budget(self, max_states: usize, max_added_events: usize) -> Self {
        let mut config = self.with_certified_time();
        config.certified_time = Some(CertifiedTimeConfig {
            max_states,
            max_added_events,
        });
        config
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
    assert!(
        !config.mailbox_time
            || ((config.time_filter || config.time_zombie)
                && !config.time_predicate
                && !config.time_canon_free),
        "mailbox timing requires terminal filtering with original MUST canonical rules"
    );
    assert!(
        config.source_order == SourceOrder::EventId || !config.time_predicate,
        "custom source order is incompatible with time_predicate"
    );
    assert!(
        config.certified_time.is_none()
            || ((config.time_filter || config.time_zombie)
                && !config.time_predicate
                && !config.time_canon_free
                && !config.stop_on_error),
        "certified timing requires collect_errors() or with_stop_on_terminal_error(), time_filter or time_zombie, and \
         original canonical rules (no time_predicate or time_canon_free)"
    );
    // B1 (engine_plan §3): the time filter needs the whole error-subtree to stay explorable,
    // because a realizable terminal can be reachable only by a backward revisit out of a
    // time-infeasible error graph. `stop_on_error` truncates those subtrees, so the
    // combination is rejected up front — for both the sequential and the parallel path.
    assert!(
        !(config.time_filter && config.stop_on_error),
        "Config::with_time_filter() requires collect_errors() or with_stop_on_terminal_error(): time-infeasible error \
         prefixes must stay explorable (revisit completeness)"
    );
    // T2 (T2_PLAN §5): `with_time_predicate` needs the whole error subtree explorable for the
    // same revisit-completeness reason as `with_time_filter`.
    assert!(
        !(config.time_predicate && config.stop_on_error),
        "Config::with_time_predicate() requires collect_errors() or with_stop_on_terminal_error(): eager-infeasible error \
         prefixes must stay explorable (revisit completeness)"
    );
    // The filter (post-hoc on terminals) and the predicate (drives the search) are two distinct
    // regimes for the time extension; running both at once is meaningless and unsupported.
    assert!(
        !(config.time_filter && config.time_predicate),
        "Config::with_time_filter() and with_time_predicate() are mutually exclusive"
    );
    // Zombie (T2_ORACLE_SPEC Part 2): the same revisit-completeness requirement as the filter
    // (its `record` routing IS the filter's), and a third mutually-exclusive regime.
    assert!(
        !(config.time_zombie && config.stop_on_error),
        "Config::with_time_zombie() requires collect_errors() or with_stop_on_terminal_error(): time-infeasible error \
         prefixes must stay explorable (revisit completeness)"
    );
    assert!(
        !(config.time_zombie && (config.time_filter || config.time_predicate)),
        "Config::with_time_zombie() is mutually exclusive with with_time_filter() and \
         with_time_predicate()"
    );

    if config.threads > 1 {
        parallel::explore_parallel(make_program, observer, config);
        return;
    }

    let program = CachedProgram::new(make_program());
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
        prefix_namespace: program
            .prefix_namespace()
            .filter(|&namespace| namespace != 0),
        terminal_tokens: Vec::new(),
        terminal_labels: Vec::new(),
        observer,
        buffer_added_events: observer.allows_buffered_events(),
        buffered_events_added: 0,
        priorities,
        source_order: config.source_order,
        stop_on_error: config.stop_on_error,
        stop_on_terminal_error: config.stop_on_terminal_error,
        max_executions: config.max_executions,
        max_sends: config.max_sends,
        receive_tail: config.receive_tail,
        time_filter: config.time_filter,
        mailbox_time: config.mailbox_time,
        time_predicate: config.time_predicate,
        time_level: config.time_predicate_level,
        canon_free: config.time_canon_free,
        time_zombie: config.time_zombie,
        certified_time: config.certified_time,
        frozen_cache: frozen::FrozenCache::default(),
        viable_memo: crate::time::ViableMemo::new(),
        terminal_count: 0,
        terminals_recorded: 0,
        stop: false,
        fork: None,
    };
    explorer.visit(&mut ExecutionGraph::new());
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
    prefix_namespace: Option<u64>,
    // Per-worker storage reused by borrowed terminal callbacks.
    terminal_tokens: Vec<u64>,
    terminal_labels: Vec<crate::program::TraceLabel>,
    pub(crate) observer: &'a O,
    buffer_added_events: bool,
    buffered_events_added: usize,
    pub(crate) priorities: Vec<Tid>,
    stop_on_error: bool,
    stop_on_terminal_error: bool,
    max_executions: Option<usize>,
    max_sends: Option<usize>,
    receive_tail: Option<receive_tail::ReceiveTailBudget>,
    /// Suppress non-eager-time-realizable terminals ([`Config::time_filter`]). Read only in
    /// [`record`](Self::record); `eager_feasible` is a pure function of the graph, so this
    /// carries no cross-branch state and is safe to copy into every parallel worker.
    time_filter: bool,
    mailbox_time: bool,
    /// Drive the full eager-time predicate search ([`Config::time_predicate`]). Threaded into
    /// [`pick`](crate::scheduler::pick) (T-DES), [`visit_recv`](Self::visit_recv) (T-PRED),
    /// [`visit_send`](Self::visit_send)/[`backward_revisits`](Self::backward_revisits) (T-GATE)
    /// and [`get_cons_tiebreaker`](crate::explorer::revisit::get_cons_tiebreaker) (T-CANON). Pure
    /// per-graph, so it too is safe to copy into every parallel worker.
    pub(crate) time_predicate: bool,
    /// Ladder level ([`Config::time_predicate_level`], `C1_HARDENING_SPEC` §D.4). Meaningful only
    /// while `time_predicate` is set; `4` (the default) is the shipping regime, where every
    /// `time_level >= k` test below is trivially true and the walk is byte-identical to the
    /// pre-ladder explorer. Consulted in exactly three places — T-PRED in
    /// [`visit_recv`](Self::visit_recv) (`>= 3`), T-GATE in [`visit_send`](Self::visit_send) and
    /// [`backward_revisits`](Self::backward_revisits) (`>= 4`), and the `record` debug-assert
    /// that level 4 never needs the terminal filter — which is the whole ladder.
    ///
    /// Deliberately *not* consulted by the canon (T-CANON's `(avail_lb, tid, idx)` order and the
    /// `viable`/`viable_recv` PASS oracle): the canon is one mechanism, switched on as a unit at
    /// level 2, and the oracle's own internal gate is part of it. The "T-GATE" column of §D.4 is
    /// the explorer's line-9/13 gate only.
    pub(crate) time_level: u8,
    /// `L2′` / Т-RED′'s `T2⁰` ([`Config::time_canon_free`]): arms 18, 19 and 22 of
    /// [`revisit_condition`](crate::explorer::revisit) are `true`. Read there and nowhere else.
    pub(crate) canon_free: bool,
    /// The zombie regime ([`Config::time_zombie`]): DES insertion order + the T1 terminal
    /// filter, everything else untimed. Read in [`visit_step`](Self::visit_step) (the des bit of
    /// [`pick`](crate::scheduler::pick)) and [`record`](Self::record) only.
    pub(crate) time_zombie: bool,
    /// Immutable per-worker limits; proof checks carry no shared ownership state.
    certified_time: Option<CertifiedTimeConfig>,
    source_order: SourceOrder,
    /// One timing-result cache per worker; immutable anchors are derived afresh from
    /// each graph, including after donated tasks and backward cuts.
    frozen_cache: frozen::FrozenCache,
    /// Memo of the existential canon oracle ([`crate::time::viable`], T2_ORACLE_SPEC §1.3),
    /// used by the nondet arm of `RevisitCondition` under `time_predicate`. Per worker (this
    /// struct is per worker), so the memo is effectively sharded across a parallel run; a
    /// cached verdict is a pure function of its key, so sharding only costs duplicate work,
    /// never correctness.
    pub(crate) viable_memo: crate::time::ViableMemo,
    /// This worker's own full+blocked count, for the sequential `max_executions` cap.
    pub(crate) terminal_count: usize,
    /// Running total of terminals *reported* (`on_execution`, i.e. full+blocked+error, never a
    /// filtered one). The dead-branch detector (T2_PLAN §5а) snapshots this around each
    /// [`visit_step`](Self::visit_step) to tell whether that Visit's subtree bore any terminal.
    /// Reliable only on the sequential path (a donated subtree records on another worker).
    pub(crate) terminals_recorded: usize,
    /// Set once the run should unwind: an `exit`-on-error or the execution cap.
    pub(crate) stop: bool,
    /// `Some` under a parallel run: later sibling branches are shed to the shared work
    /// queue when another worker is idle, instead of being explored inline. `None` is the
    /// sequential path (see [`Explorer::branch`]).
    pub(crate) fork: Option<Arc<Spawner>>,
}

impl<P: Program, O: Observer> Drop for Explorer<'_, P, O> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            if let Some(spawner) = &self.fork {
                // An interrupted visit cannot call complete(). Wake idle workers
                // before flushing, so the scope can join and propagate the panic.
                spawner.request_stop();
            }
        }
        let count = std::mem::take(&mut self.buffered_events_added);
        if count != 0 {
            self.observer.on_events_added_batch(count);
        }
    }
}

impl<P: Program, O: Observer> Explorer<'_, P, O> {
    #[inline]
    fn event_added(&mut self, graph: &ExecutionGraph, event: EventId) {
        if self.buffer_added_events {
            // Atomic counters wrap as well; keep their behavior in debug builds.
            self.buffered_events_added = self.buffered_events_added.wrapping_add(1);
        } else {
            self.observer.on_event_added(graph, event);
        }
    }
    /// `Visit_P(G)` (Algorithm 1, lines 2-14), building the per-thread `(traces, nexts)`
    /// state from scratch. `g` is consistent on entry (its caller tested it — line 7's
    /// `consistent_after_recv`, line 13's `consistent` — or it is the empty graph). Used
    /// wherever the parent's state does
    /// not carry over: the root, a subtree taken from the work queue, and after a backward
    /// revisit restructures the graph.
    pub(crate) fn visit(&mut self, g: &mut ExecutionGraph) {
        if self.stopping() {
            return;
        }
        // `traces[i]` is thread `i`'s per-event trace, `nexts[i]` its next event under that
        // trace. Both are threaded down the recursion; adding an event mutates only the
        // acting thread's entry, so only that thread's next is recomputed.
        let mut traces = pooled_traces_of(g, self.program.num_threads());
        let mut read = ForwardReads::new(
            g,
            self.program.num_threads(),
            !self.observer.observes_rejected_rf_trials(),
        );
        let mut nexts = if let Some(namespace) = self.prefix_namespace {
            g.reset_program_prefix_namespace(namespace);
            (0..self.program.num_threads())
                .map(|tid| {
                    let restored = g
                        .program_prefix(tid)
                        .and_then(|token| self.program.next_thread_at_prefix(tid, token));
                    let (next, cursor) = match restored {
                        Some((next, cursor)) => (next, Some(cursor)),
                        None => self.program.next_thread_cursor(tid, &traces[tid]),
                    };
                    debug_assert_eq!(
                        next,
                        self.program.next_thread(tid, &traces[tid]),
                        "persistent prefix changed the full-trace next event"
                    );
                    if g.thread_len(tid) != 0 {
                        let token = cursor
                            .and_then(|cursor| self.program.persist_cursor(tid, cursor))
                            .filter(|&token| token != 0)
                            .unwrap_or(0);
                        g.set_program_prefix(EventId::new(tid, g.thread_len(tid) - 1), token);
                    }
                    read.set_cursor(tid, cursor);
                    next
                })
                .collect()
        } else {
            self.program.next(&traces)
        };
        self.visit_step(g, &mut traces, &mut nexts, &mut read);
    }

    /// `Visit_P(G)` given the already-computed `(traces, nexts)`. Picks the next event from
    /// `nexts` (addability is still rechecked against `g`) and dispatches. The forward cases
    /// derive the child's state in place; error and the backward-revisit case rebuild it via
    /// [`visit`](Self::visit).
    fn visit_step(
        &mut self,
        g: &mut ExecutionGraph,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
        read: &mut ForwardReads,
    ) {
        if self.stopping() {
            return;
        }
        debug_assert!(
            *traces == traces_of(g, self.program.num_threads())
                && *nexts == self.program.next(traces),
            "threaded traces/nexts drifted from a fresh recompute"
        );
        debug_assert!(
            read.matches_graph(g),
            "threaded RF marks/counters drifted from the committed graph"
        );
        for next in nexts.iter().filter_map(ThreadNext::label) {
            if self.mailbox_time {
                assert!(
                    !matches!(
                        next,
                        Label::Send {
                            model: crate::Model::Cd,
                            ..
                        }
                    ),
                    "mailbox timing does not support Cd sends"
                );
                assert!(
                    next.blocking() != Some(false) || next.is_timed_recv(),
                    "mailbox timing requires an explicit timeout or poll window on nonblocking receives"
                );
            } else if self.time_filter || self.time_zombie || self.time_predicate {
                assert!(
                    !next.is_timed_recv(),
                    "timed receives in exploration require Config::with_mailbox_time()"
                );
            }
        }
        // Dead-branch detector (T2_PLAN §5а): a `visit_step` call *is* one logical Visit_P(G)
        // node (every logical Visit reaches exactly one `visit_step`, via `visit` or
        // `branch_memo`). Snapshot the running terminal count so `on_visit_exit` can report
        // whether this Visit's whole subtree bore a terminal — `record` (which recurses on the
        // same `self`) bumps `terminals_recorded`, so the delta is the subtree's terminal count.
        self.observer.on_visit_enter(g);
        let terminals_before = self.terminals_recorded;
        if self.certified_prune(g) {
            // A certificate examines this Visit too. Count its boundary vertex and
            // classify it as barren rather than hiding pruning work from observers.
            self.observer.on_visit_exit(g, false);
            return;
        }
        // The des bit: both the predicate (T-DES) and the zombie regime run under the DES
        // insertion order; zombie changes nothing else about the walk.
        match pick_with_read_marks(
            g,
            nexts,
            &self.priorities,
            self.time_predicate || self.time_zombie,
            self.mailbox_time,
            read,
            Some(&read.unread),
        ) {
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
                self.record(g, kind, Some(traces));
            }
            NextStep::Event { tid, label } => match &label {
                // line 5: error - see `visit_error`.
                Label::Error { .. } => self.visit_error(g, tid, label),
                // line 6: nondet - enumerate every value of the option set.
                Label::Nondet { .. } => self.visit_nondet(g, tid, label, traces, nexts, read),
                // line 7: receive - enumerate rf sources.
                Label::Recv { .. } => {
                    if !self.try_receive_tail(g, traces, nexts, read) {
                        self.visit_recv(g, tid, label, traces, nexts, read);
                    }
                }
                // lines 8-13: send - the no-revisit branch plus backward revisits.
                Label::Send { .. } => self.visit_send(g, tid, label, traces, nexts, read),
            },
        }
        debug_assert!(
            read.matches_graph(g),
            "a child changed its parent's RF state"
        );
        self.observer
            .on_visit_exit(g, self.terminals_recorded > terminals_before);
    }

    /// Omit only this forward subtree; ancestor send calls still run their
    /// backward-revisit loops. The certificate excludes future sends, so no
    /// backward-revisit construction can originate inside the omitted suffix.
    fn try_receive_tail(
        &mut self,
        graph: &ExecutionGraph,
        traces: &[Vec<Option<Val>>],
        nexts: &[ThreadNext],
        read: &ForwardReads,
    ) -> bool {
        let Some(budget) = self.receive_tail else {
            return false;
        };
        if self.time_filter
            || self.time_zombie
            || self.time_predicate
            || self.mailbox_time
            || budget.max_states == 0
            || budget.max_pending_per_thread == 0
            || !nexts.iter().all(receive_tail::receive_or_finished)
            || read.unread.iter().sum::<usize>() < 2
            || read
                .unread
                .iter()
                .any(|&count| count > budget.max_pending_per_thread.min(64))
        {
            return false;
        }
        self.fill_terminal_labels(graph, Some(traces));
        if !self
            .observer
            .receive_tail_candidate(graph, &self.terminal_labels)
        {
            return false;
        }
        let Some(certificate) = receive_tail::certify(
            self.program,
            graph,
            traces,
            nexts,
            &self.terminal_labels,
            budget,
        ) else {
            return false;
        };
        if !self.observer.accept_receive_tail(&certificate) {
            return false;
        }
        self.observer.on_receive_tail_pruned(&certificate);
        true
    }

    /// Prune a whole construction subtree only when both layers certify it. Forward
    /// impossibility alone cannot discard a path that discovers a repairing revisit.
    /// The coverage layer checks the same original canonical helper used by the main
    /// explorer and conservatively refuses any admitted escape. Unknown leaves the
    /// original search untouched. All certificates are freshly bound to this program,
    /// graph, construction stamps, and policy; none are reused across revisits.
    fn certified_prune(&mut self, g: &ExecutionGraph) -> bool {
        use crate::observer::{TimeCertificateEvent, TimeCertificateOutcome};
        use crate::time::future::{check_completion, CompletionCheck, LookaheadBudget};
        use ownership::{certify_no_escape_with_order, OwnershipBudget, OwnershipCheck};

        let Some(limits) = self.certified_time else {
            return false;
        };
        if limits.max_states == 0 || limits.max_added_events == 0 {
            return false;
        }
        // Without an existing blocking consumption, there is no old eager race for
        // these certificates to reject. Skipping the check only forgoes pruning.
        if !self.mailbox_time && !g.iter_recvs().any(|r| g.label(r).blocking() == Some(true)) {
            return false;
        }
        let frozen = self.frozen_cache.check_with_time_semantics(
            g,
            self.program,
            limits.max_added_events,
            self.source_order,
            self.mailbox_time,
        );
        self.observer.on_frozen_time(g, &frozen);
        if frozen.outcome == crate::observer::FrozenTimeOutcome::Pruned {
            return true;
        }
        // The older semantic/coverage fallback assumes transparent NB receives.
        // New timing uses the immutable-core and first-alteration certificates only.
        if self.mailbox_time {
            return false;
        }
        let completion = check_completion(
            g,
            self.program,
            LookaheadBudget {
                max_states: limits.max_states,
                max_added_events: limits.max_added_events,
            },
        );
        let mut event = TimeCertificateEvent {
            outcome: TimeCertificateOutcome::CompletionUnknown,
            completion_states: completion.stats().expanded_states,
            completion_events: completion.stats().added_events,
            completion_cases: completion.stats().expanded_cases,
            completion_temporal_checks: completion.stats().temporal_checks,
            ownership_states: 0,
            ownership_events: 0,
            ownership_temporal_checks: 0,
            revisit_candidates: 0,
            canonical_checks: 0,
        };
        let pruned = match completion {
            CompletionCheck::Unknown(_) => false,
            CompletionCheck::Witness(_) => {
                event.outcome = TimeCertificateOutcome::CompletionWitness;
                false
            }
            CompletionCheck::Impossible(certificate) => {
                debug_assert!(certificate.applies_to(g));
                let coverage = certify_no_escape_with_order(
                    self.program,
                    g,
                    &self.priorities,
                    self.time_zombie,
                    OwnershipBudget {
                        max_states: limits.max_states,
                        max_added_events: limits.max_added_events,
                    },
                    self.source_order,
                );
                event.ownership_states = coverage.stats().states;
                event.ownership_events = coverage.stats().added_events;
                event.ownership_temporal_checks = coverage.stats().forward_terminals;
                event.revisit_candidates = coverage.stats().revisit_candidates;
                event.canonical_checks = coverage.stats().canonical_checks;
                match coverage {
                    OwnershipCheck::Certified(proof) => {
                        debug_assert!(proof.applies_to_with_order(
                            g,
                            &self.priorities,
                            self.time_zombie,
                            self.source_order
                        ));
                        event.outcome = TimeCertificateOutcome::Pruned;
                        true
                    }
                    OwnershipCheck::Unknown { .. } | OwnershipCheck::FeasibleTerminal { .. } => {
                        event.outcome = TimeCertificateOutcome::OwnershipUnknown;
                        false
                    }
                }
            }
        };
        self.observer.on_time_certificate(g, &event);
        pruned
    }

    /// Append `entry` to thread `tid`'s trace, recompute just that thread's next event, run
    /// `body` with updated traces, nexts and its continuation sidecar, then restore all three. `entry` is the value the
    /// new event contributes to its thread's trace: the value a receive read (`None` = ⊥), a
    /// nondet's chosen value, or `None` for a send/error.
    #[allow(clippy::too_many_arguments)]
    fn with_child_memo(
        &mut self,
        graph: &mut ExecutionGraph,
        tid: Tid,
        entry: Option<Val>,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
        read: &mut ForwardReads,
        body: impl FnOnce(
            &mut Self,
            &mut ExecutionGraph,
            &mut Vec<Vec<Option<Val>>>,
            &mut Vec<ThreadNext>,
            &mut ForwardReads,
        ),
    ) {
        traces[tid].push(entry);
        let saved_cursor = read.cursor(tid);
        let (next, cursor) = saved_cursor
            .and_then(|cursor| self.program.advance_thread(tid, cursor, entry))
            .map(|(next, cursor)| (next, Some(cursor)))
            .unwrap_or_else(|| self.program.next_thread_cursor(tid, &traces[tid]));
        debug_assert_eq!(
            next,
            self.program.next_thread(tid, &traces[tid]),
            "cursor continuation changed the full-trace next event"
        );
        let saved = std::mem::replace(&mut nexts[tid], next);
        read.set_cursor(tid, cursor);
        if self.prefix_namespace.is_some() {
            let token = cursor
                .and_then(|cursor| self.program.persist_cursor(tid, cursor))
                .filter(|&token| token != 0)
                .unwrap_or(0);
            graph.set_program_prefix(EventId::new(tid, traces[tid].len() - 1), token);
        }
        body(self, graph, traces, nexts, read);
        nexts[tid] = saved;
        read.set_cursor(tid, saved_cursor);
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
    fn branch(&mut self, first: &mut bool, g: &mut ExecutionGraph) {
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
        g: &mut ExecutionGraph,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
        read: &mut ForwardReads,
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
        self.visit_step(g, traces, nexts, read);
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
    fn visit_error(&mut self, g: &mut ExecutionGraph, tid: Tid, label: Label) {
        let checkpoint = g.checkpoint();
        let e = g.add_event(tid, label);
        self.event_added(g, e);
        if self.stop_on_error {
            self.record(g, ExecutionKind::Error, None);
            self.request_stop();
        } else {
            // The error event is now in the trace, so this thread's `next` returns
            // Finished: the recursion cannot re-pick it and cannot run past it. A single
            // child, so it is always explored inline (never donated).
            self.visit(g);
        }
        g.restore_append(checkpoint, e);
    }

    /// line 7: `for s in G.S union {bottom} do VisitIfConsistent(SetRF(G, e, s))`.
    ///
    /// Every send plus bottom (the no-message source) is tried. Wrong-destination sends
    /// and blocking bottom choices are rejected by well-formedness; graph-agnostic
    /// observers can report those trials without storing the rejected RF edge. Every
    /// source still emits its original callbacks. Non-blocking bottom remains eligible.
    fn visit_recv(
        &mut self,
        g: &mut ExecutionGraph,
        tid: Tid,
        label: Label,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
        read: &mut ForwardReads,
    ) {
        let checkpoint = g.checkpoint();
        let e = g.add_event(tid, label);
        // Discipline (graph.rs): assign an rf immediately after adding a receive.
        g.set_rf_forward(e, None);
        self.event_added(g, e);

        // Sources in a deterministic order: sends in (tid, idx) order, then bottom. The
        // enumeration order does not affect the set of explored executions (each rf source
        // is a distinct child, visited once), so the natural event order suffices.
        // Snapshot sources before descending: children append/pop on this same
        // graph. Small bounded protocols need no allocation for this snapshot.
        let mut inline = [None; 32];
        let mut overflow = Vec::new();
        // Opt-in observers need no callbacks for universally inconsistent
        // wrong-destination/already-consumed sources. The maintained destination
        // index is their exact ordered subsequence of the ordinary send list.
        let indexed = read.sources.as_ref().map(|rows| rows[tid].as_slice());
        let source_count = indexed.map_or(g.num_sends(), <[EventId]>::len);
        let sources = if source_count < inline.len() {
            if let Some(indexed) = indexed {
                for (slot, &send) in inline.iter_mut().zip(indexed) {
                    *slot = Some(send);
                }
            } else {
                for (slot, send) in inline.iter_mut().zip(g.iter_sends()) {
                    *slot = Some(send);
                }
            }
            &inline[..source_count + 1]
        } else {
            if let Some(indexed) = indexed {
                overflow.extend(indexed.iter().copied().map(Some));
            } else {
                overflow.extend(g.iter_sends().map(Some));
            }
            overflow.push(None); // bottom
            overflow.as_slice()
        };

        // The freshly appended receive has not committed a source yet. The
        // parent's maintained marks are exactly the reads of all other receives.

        // Each inline child restores this exact graph before returning. Donated
        // subtrees and observer snapshots own COW clones, so changing the next
        // source cannot change an already explored or queued sibling.
        let mut first = true;
        let materialize_rejected = self.observer.inspects_rf_trial_graphs();
        let blocking = g.label(e).blocking() == Some(true);
        for &src in sources {
            if self.stopping() {
                break;
            }
            if !materialize_rejected
                && src.map_or(blocking, |source| g.label(source).dst() != Some(tid))
            {
                // Neither rejection evaluates a predicate or temporal/model clause
                // in the original consistency check. Preserve every trial notification,
                // including blocking bottom, without changing valid-source handling.
                self.observer.on_rf_choice(g, e, src);
                self.observer.on_inconsistent(g);
                continue;
            }
            g.set_rf_forward(e, src);
            self.observer.on_rf_choice(g, e, src);
            // `e` is the freshly added maximal receive, so only clauses mentioning it can
            // break: the incremental `consistent_after_recv` suffices. Filter here, before
            // the `(traces, nexts)` update, so a rejected source costs no recompute.
            let cons = crate::consistency::consistent_after_recv_with(g, e, read);
            debug_assert_eq!(
                cons,
                consistent(g),
                "incremental recv-consistency must agree with the full check"
            );
            // T-PRED (T2_PLAN §2a, §5): under the eager-time predicate an rf-fork is taken only
            // when the resulting *prefix* is eager-time-feasible, not merely consistent —
            // `time::check` is a RAW feasibility test of `base` (NOT forced_closure; that gate is
            // only sound on forward sends / revisits, T2_PLAN §5). This is what keeps the search
            // out of the eager-infeasible superset; it is completeness-safe only in concert with
            // T-DES (Lemma 1: the earlier-time siblings are already present when `e` is woken).
            // `check` is called only on a `consistent` base (short-circuit), so a blocking recv
            // reading ⊥ — which is inconsistent — never reaches the time system.
            //
            // Ladder (§D.4): T-PRED is the level-3 rung, so levels 2 (canon only) and below run
            // the plain consistency test here. Dropping a *pruner* can only add children, never
            // remove one (M2, §0.2), so a lower rung explores a superset of level 4's tree.
            let ok = if self.time_predicate && self.time_level >= 3 {
                cons && crate::time::check(g).is_feasible()
            } else {
                cons
            };
            if !ok {
                self.observer.on_inconsistent(g);
                continue;
            }
            // Trace entry for `e`: the value it read (`None` for a ⊥/timeout read).
            let entry = src.map(|s| g.label(s).payload().expect("send carries a payload"));
            if let Some(source) = src {
                read.consume(tid, source);
            }
            self.with_child_memo(
                g,
                tid,
                entry,
                traces,
                nexts,
                read,
                |this, g, traces, nexts, read| {
                    this.branch_memo(&mut first, g, traces, nexts, read);
                },
            );
            if let Some(source) = src {
                read.restore_consume(tid, source);
            }
        }
        g.restore_append(checkpoint, e);
    }

    /// line 6: `case e in ND: for v in S do Visit_P(SetND(G, e, v))`.
    ///
    /// A nondet event enumerates every value of its finite option set. Each choice recurses
    /// through plain `Visit_P`, not `VisitIfConsistent`: a nondet value never participates
    /// in rf / well-formedness / the model predicates, so `g` being consistent on entry
    /// makes every `SetND` result consistent by construction.
    fn visit_nondet(
        &mut self,
        g: &mut ExecutionGraph,
        tid: Tid,
        label: Label,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
        read: &mut ForwardReads,
    ) {
        let checkpoint = g.checkpoint();
        let e = g.add_event(tid, label);
        self.event_added(g, e);

        // `Label::nondet` canonicalised the set to sorted+unique, so this explores
        // min(S) first (the line-19 canonical value) and each value exactly once.
        let set = g
            .label(e)
            .nd_set()
            .expect("visit_nondet on a non-nondet label")
            .to_vec();
        // Reuse one graph across all values (see `visit_recv`), re-pointing `e`'s nondet
        // choice in place.
        let mut first = true;
        for v in set {
            if self.stopping() {
                break;
            }
            g.set_nd(e, v);
            // A nondet event's trace entry is its chosen value.
            self.with_child_memo(
                g,
                tid,
                Some(v),
                traces,
                nexts,
                read,
                |this, g, traces, nexts, read| {
                    this.branch_memo(&mut first, g, traces, nexts, read);
                },
            );
        }
        g.restore_append(checkpoint, e);
    }

    /// lines 8-13: add the send, explore the no-revisit branch (line 9), then attempt every
    /// backward revisit (lines 10-13). The revisit loop runs on `g_add` regardless of
    /// whether line 9's graph was consistent - Algorithm 1 does not gate it, and a revisit
    /// can delete the very events that made `g_add` inconsistent.
    fn visit_send(
        &mut self,
        g: &mut ExecutionGraph,
        tid: Tid,
        label: Label,
        traces: &mut Vec<Vec<Option<Val>>>,
        nexts: &mut Vec<ThreadNext>,
        read: &mut ForwardReads,
    ) {
        if let Some(limit) = self.max_sends {
            if g.num_sends() >= limit {
                // This also skips potential repairing revisits. Report incomplete
                // search even for a currently time-infeasible construction prefix;
                // never route this through the terminal timing filter.
                self.observer.on_send_limit(g, limit);
                if self.observer.should_stop() {
                    self.request_stop();
                }
                return;
            }
        }
        let checkpoint = g.checkpoint();
        let e = g.add_event(tid, label);
        read.send_added(g, e);
        self.event_added(g, e);

        // The line-9 child and every backward-revisit child are siblings of this send
        // node, so they share one `first` flag (the first explored inline, the rest
        // donatable).
        let mut first = true;
        // line 9: `e` is simply added. A ≤_G-maximal *unread* send is consistent in every
        // model (it is so-after everything in its thread / has no porf-successors, so it
        // cannot be the `u` of clause (b), never appears in clause (c), and has no outgoing
        // edge in the mbox graph). So branch unconditionally rather than re-checking the
        // whole graph; the debug assertion guards the proof.
        //
        // T-GATE (T2_PLAN §2c, line 9): under the eager-time predicate the added early-time
        // send can make the *obligatory* continuation eager-infeasible even though `g_add`
        // itself is (still untimed-consistent and) feasible — the refuted-L3 case. So the
        // forward branch is taken only when `forced_closure(g_add)` is feasible: the closure
        // adds every event the policy is forced to add with no genuine rf-fork, and if *that* is
        // infeasible the whole forward subtree is fruitless. The revisit loop below runs
        // regardless (a revisit can delete the very events that broke the closure).
        if !self.stopping() {
            //
            // Ladder (§D.4): T-GATE is the level-4 rung; below it the forward branch is taken
            // unconditionally, exactly as untimed. The `consistent` debug-assert stays valid on
            // every rung — it is a property of a ≤_G-maximal unread send, not of the regime.
            let forward_ok = if self.time_predicate && self.time_level >= 4 {
                crate::time::gate_feasible_cached(
                    g,
                    self.program,
                    &self.priorities,
                    &mut self.viable_memo,
                )
            } else {
                debug_assert!(
                    consistent(g),
                    "line-9 maximal unread send must be consistent"
                );
                true
            };
            if forward_ok {
                // A send contributes no read value to its thread's trace.
                self.with_child_memo(
                    g,
                    tid,
                    None,
                    traces,
                    nexts,
                    read,
                    |this, g, traces, nexts, read| {
                        this.branch_memo(&mut first, g, traces, nexts, read);
                    },
                );
            }
        }
        // lines 10-13. A backward revisit restructures the graph, so its children take the
        // fresh `visit` path rather than a derived state.
        if !self.stopping() {
            self.backward_revisits(&mut first, g, e);
        }
        read.send_removed(g, e);
        g.restore_append(checkpoint, e);
    }

    fn fill_terminal_labels(
        &mut self,
        graph: &ExecutionGraph,
        traces: Option<&[Vec<Option<Val>>]>,
    ) {
        self.terminal_tokens.clear();
        self.terminal_labels.clear();
        let mut available = self
            .prefix_namespace
            .is_some_and(|namespace| namespace == graph.program_prefix_namespace());
        if available {
            for tid in 0..self.program.num_threads() {
                let Some(token) = graph.program_prefix(tid) else {
                    available = false;
                    break;
                };
                self.terminal_tokens.push(token);
            }
        }
        if !available
            || !self
                .program
                .labels_at_prefixes_into(&self.terminal_tokens, &mut self.terminal_labels)
        {
            // Never expose annotations from an earlier terminal or a partial
            // unsuccessful prefix lookup, even when falling back after eviction.
            self.terminal_labels.clear();
            let labels = match traces {
                Some(traces) => self.program.labels(traces),
                None => self
                    .program
                    .labels(&pooled_traces_of(graph, self.program.num_threads())),
            };
            self.terminal_labels.extend(labels);
        }
    }

    /// Record a terminal execution and honour terminal stopping rules. Returns whether the
    /// terminal was reported (`true`) or suppressed by the eager time filter (`false`).
    ///
    /// This is the single funnel every terminal (sequential and parallel; full, blocked or
    /// error) passes through, so it is also the only place the time filter needs to sit.
    /// Under [`Config::time_filter`] a terminal whose graph is not eager-time-realizable is
    /// routed to `on_execution_filtered` and counts towards neither `terminal_count` nor
    /// `max_executions` (engine_plan §3): a suppressed terminal is not an execution of the
    /// timed program.
    fn record(
        &mut self,
        graph: &ExecutionGraph,
        kind: ExecutionKind,
        traces: Option<&[Vec<Option<Val>>]>,
    ) -> bool {
        let timed = self.time_filter || self.time_zombie || self.time_predicate;
        if !timed && self.observer.accepts_execution_view() {
            self.fill_terminal_labels(graph, traces);
            self.observer
                .on_execution_view(graph, &self.terminal_labels, kind);
        } else {
            let persistent_labels = self
                .prefix_namespace
                .filter(|&namespace| namespace == graph.program_prefix_namespace())
                .and_then(|_| {
                    (0..self.program.num_threads())
                        .map(|tid| graph.program_prefix(tid))
                        .collect::<Option<Vec<_>>>()
                })
                .and_then(|tokens| self.program.labels_at_prefixes(&tokens));
            let labels = persistent_labels.unwrap_or_else(|| match traces {
                Some(traces) => self.program.labels(traces),
                None => self
                    .program
                    .labels(&pooled_traces_of(graph, self.program.num_threads())),
            });
            let exec = Execution::new(graph.clone()).with_labels(labels);
            if timed {
                // The v1 model guard is a precondition of the time extension, not an invariant of
                // any regime, so it runs on every timed terminal regardless of level or profile.
                let feasible = if self.mailbox_time {
                    // Feasibility only: the same verdict as `check_mailbox(..).is_feasible()`
                    // (which it re-runs in full on the accepted case), without building the
                    // explanation tables for the rejected one.
                    crate::time::eager_mailbox_feasible(exec.graph())
                } else {
                    crate::time::assert_supported_models(exec.graph());
                    crate::time::eager_feasible(exec.graph())
                };
                if !feasible {
                    // T-GATE / record (T2_PLAN §2c): under the predicate at level 4 every terminal
                    // reached is eager-feasible by construction (T-PRED gates receives, T-GATE gates
                    // sends / revisits), so landing here at all is a bug in that invariant. Debug
                    // builds say so loudly; release builds still must not *print* the terminal,
                    // because a model checker reporting an unrealizable counterexample is worse than
                    // one reporting too few - so it takes the filtered path either way, where
                    // `on_execution_filtered` keeps it visible rather than silently dropped.
                    debug_assert!(
                        !(self.time_predicate && self.time_level >= 4),
                        "T2 terminal must be eager-feasible (predicate invariant)"
                    );
                    // Ladder levels 2-3 (§D.4): with T-PRED and/or T-GATE off the walk *does* reach
                    // unrealizable terminals, so they are routed through the same post-filter the
                    // zombie regime uses — which is what makes `realizable(L2) == realizable(L4)` a
                    // meaningful set equality rather than a comparison of differently-shaped outputs.
                    // Zombie routes terminals exactly as the T1 filter does (T2_ORACLE_SPEC §2.1): an
                    // unrealizable terminal is filtered, counted in neither `terminal_count` nor
                    // `max_executions`.
                    self.observer.on_execution_filtered(&exec, kind);
                    return false;
                }
            }
            self.observer.on_execution(&exec, kind);
        }
        if self.observer.should_stop() {
            self.request_stop();
        }
        // Counts every reported terminal (full/blocked/error) for the dead-branch detector.
        self.terminals_recorded += 1;
        if matches!(kind, ExecutionKind::Full | ExecutionKind::Blocked) {
            self.terminal_count += 1;
        }
        if self.stop_on_terminal_error && kind == ExecutionKind::Error {
            self.request_stop();
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
        true
    }
}
