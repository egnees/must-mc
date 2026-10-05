//! The `next_P` scheduling policy.
//!
//! `next_P(G)` obeys the paper's three assumptions: (i) it never picks an event of a
//! blocked thread; (ii) it never adds a blocking receive when there is no matching
//! message; (iii) it yields a terminal verdict only when nothing can be added. Because
//! addability is recomputed on the current graph every call, a receive is automatically
//! rescheduled the moment a matching send appears (Example 4.1). There is no explicit
//! blocking event in the graph: a thread whose next event is a blocking receive with no
//! message is simply "blocked" at this graph, and unblocks when a send shows up.

use crate::event::{EventId, Label, Tid, Val};
use crate::graph::ExecutionGraph;
use crate::program::{Program, ThreadNext};

/// What `next_P(G)` yields.
pub enum NextStep {
    /// The next event to add for thread `tid` (the highest-priority addable thread).
    Event { tid: Tid, label: Label },
    /// Nothing is addable. `blocked` lists the threads stuck on a blocking receive with
    /// no message: empty means every thread is finished, so the execution is *full*;
    /// non-empty means it is *blocked*.
    Terminal { blocked: Vec<Tid> },
}

/// Extract `trace_G(i)` for every thread: one value per event in po, `Some(v)` for a
/// receive that read value `v`, `None` for a send/error or a receive that read nothing.
pub fn traces_of(g: &ExecutionGraph, num_threads: usize) -> Vec<Vec<Option<Val>>> {
    let mut traces = Vec::new();
    fill_traces(g, num_threads, &mut traces);
    traces
}

fn fill_traces(g: &ExecutionGraph, num_threads: usize, traces: &mut Vec<Vec<Option<Val>>>) {
    traces.resize_with(num_threads, Vec::new);
    for (tid, trace) in traces.iter_mut().enumerate() {
        let len = g.thread_len(tid);
        trace.clear();
        trace.reserve(len);
        for idx in 0..len {
            let e = EventId::new(tid, idx);
            let entry = match g.label(e) {
                Label::Recv { .. } => g.reads_from(e).and_then(|s| g.label(s).payload()),
                // A nondet event's slot is its chosen value, always set by replay time.
                Label::Nondet { .. } => {
                    Some(*g.nd_value(e).expect("ND event must have a chosen value"))
                }
                Label::Send { .. } | Label::Error { .. } => None,
            };
            trace.push(entry);
        }
    }
}

thread_local! {
    static TRACE_POOL: std::cell::RefCell<Vec<Vec<Vec<Option<Val>>>>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Owned scratch, so nested visits never alias their parent's trace buffers.
/// Only idle vectors live in the per-worker pool; no RefCell borrow spans replay,
/// observer callbacks, or recursion. Bound idle retention independently of depth.
pub(crate) struct PooledTraces(Vec<Vec<Option<Val>>>);

impl std::ops::Deref for PooledTraces {
    type Target = Vec<Vec<Option<Val>>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for PooledTraces {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Drop for PooledTraces {
    fn drop(&mut self) {
        TRACE_POOL.with(|pool| {
            let mut pool = pool.borrow_mut();
            if pool.len() < 32 {
                pool.push(std::mem::take(&mut self.0));
            }
        });
    }
}

pub(crate) fn pooled_traces_of(g: &ExecutionGraph, num_threads: usize) -> PooledTraces {
    let mut traces = TRACE_POOL.with(|pool| pool.borrow_mut().pop().unwrap_or_default());
    fill_traces(g, num_threads, &mut traces);
    PooledTraces(traces)
}

/// Whether thread `tid`'s next event `label` can be added to `g` right now.
///
/// Sends, errors, and non-blocking receives are always addable; a blocking receive is
/// addable only when some unread send matches its predicate and destination.
fn addable(g: &ExecutionGraph, tid: Tid, label: &Label) -> bool {
    match label {
        Label::Recv { blocking: true, .. } => {
            let mut read = crate::graph::PooledMarks::take();
            crate::consistency::mark_read_sources(g, None, &mut read);
            addable_with(g, tid, label, &read)
        }
        _ => true,
    }
}

/// [`addable`] with the "which sends are already read" marks supplied by the caller.
///
/// The marks used to be recomputed inside the scan as `g.is_read(s)`, an `O(|E|)` sweep
/// **per candidate send** — so a single addability query was `O(|S| · |E|)`, and one is run
/// for every parked thread at every Visit. Marking the read sources once per `next_P`
/// decision makes it `O(|E| + |S|)`. The candidate tests are also ordered cheapest-first
/// (destination, then the mark, then the predicate), which only changes how often the
/// user's predicate closure is evaluated, never the answer.
fn addable_with(g: &ExecutionGraph, tid: Tid, label: &Label, read: &crate::graph::Marks) -> bool {
    addable_with_counts(g, tid, label, read, None)
}

fn addable_with_counts(
    g: &ExecutionGraph,
    tid: Tid,
    label: &Label,
    read: &crate::graph::Marks,
    unread: Option<&[usize]>,
) -> bool {
    match label {
        Label::Send { .. } | Label::Error { .. } => true,
        // A nondet choice is always addable; assumption (ii) constrains blocking receives only.
        Label::Nondet { .. } => true,
        // A non-blocking receive can always read nothing, so it is always addable.
        Label::Recv {
            blocking: false, ..
        } => true,
        Label::Recv {
            blocking: true,
            pred,
            ..
        } => {
            if pred.is_any() {
                if let Some(unread) = unread {
                    return unread.get(tid).is_some_and(|&count| count != 0);
                }
            }
            g.iter_sends().any(|s| {
                let lbl = g.label(s);
                lbl.dst() == Some(tid)
                    && !read.contains(s)
                    && lbl.payload().is_some_and(|v| pred.test_sym(v))
            })
        }
    }
}

/// Compute `next_P(G)`: the event of the first addable thread in `priorities` order, or
/// a terminal verdict with the list of blocked threads.
///
/// `priorities` is a permutation of `0..program.num_threads()`. The execution counts are
/// invariant to the permutation chosen.
pub fn next_step<P: Program>(program: &P, priorities: &[Tid], g: &ExecutionGraph) -> NextStep {
    let traces = traces_of(g, program.num_threads());
    let nexts = program.next(&traces);
    pick(g, &nexts, priorities, false)
}

/// The `next_P(G)` decision given the per-thread next events `nexts` already computed:
/// the first addable thread in `priorities` order, else a terminal verdict. Addability is
/// (re)checked against `g` here, not cached, so a receive unblocks the moment a matching
/// send appears.
///
/// `des` selects the discrete-event scheduling order of the time-intervals extension
/// (`pick_des`, T2_PLAN §2b) — set by both the T2 predicate and the zombie regime
/// (`des = time_predicate || time_zombie`, T2_ORACLE_SPEC §2.1); with it `false` this is the
/// ordinary priority policy and every count is byte-identical to the untimed explorer.
pub fn pick(g: &ExecutionGraph, nexts: &[ThreadNext], priorities: &[Tid], des: bool) -> NextStep {
    pick_with_time_semantics(g, nexts, priorities, des, false)
}

/// Scheduling changes construction order only; it never removes a consistent source.
/// The explicit semantics bit is needed for send-only prefixes of timed programs.
pub(crate) fn pick_with_time_semantics(
    g: &ExecutionGraph,
    nexts: &[ThreadNext],
    priorities: &[Tid],
    des: bool,
    mailbox_time: bool,
) -> NextStep {
    pick_with_optional_read(g, nexts, priorities, des, mailbox_time, None, None)
}

/// The explorer maintains these exact committed sources alongside its traces.
/// Scheduling still recomputes addability; only rebuilding the same marks is skipped.
pub(crate) fn pick_with_read_marks(
    g: &ExecutionGraph,
    nexts: &[ThreadNext],
    priorities: &[Tid],
    des: bool,
    mailbox_time: bool,
    read: &crate::graph::Marks,
    unread: Option<&[usize]>,
) -> NextStep {
    pick_with_optional_read(g, nexts, priorities, des, mailbox_time, Some(read), unread)
}

#[allow(clippy::too_many_arguments)]
fn pick_with_optional_read(
    g: &ExecutionGraph,
    nexts: &[ThreadNext],
    priorities: &[Tid],
    des: bool,
    mailbox_time: bool,
    supplied_read: Option<&crate::graph::Marks>,
    unread: Option<&[usize]>,
) -> NextStep {
    if des {
        return pick_des(g, nexts, mailbox_time, supplied_read, unread);
    }
    // The read-source marks are shared by every addability query of this decision, and are
    // built only once a blocking receive actually needs them (the common case is a thread
    // whose next event is unconditionally addable).
    let mut read: Option<crate::graph::PooledMarks> = None;
    for &tid in priorities {
        if let ThreadNext::Next(label) = &nexts[tid] {
            let addable = match label {
                Label::Recv { blocking: true, .. } => {
                    let marks: &crate::graph::Marks = match supplied_read {
                        Some(marks) => marks,
                        None => read.get_or_insert_with(|| {
                            let mut m = crate::graph::PooledMarks::take();
                            crate::consistency::mark_read_sources(g, None, &mut m);
                            m
                        }),
                    };
                    addable_with_counts(g, tid, label, marks, unread)
                }
                _ => true,
            };
            if addable {
                return NextStep::Event {
                    tid,
                    label: label.clone(),
                };
            }
        }
    }

    // Nothing addable: gather the threads parked on a blocking receive. In tid order so
    // the verdict is deterministic regardless of the priority permutation.
    NextStep::Terminal {
        blocked: blocked_threads(nexts),
    }
}

/// Threads parked on a blocking receive under `nexts`, in tid order (so the terminal verdict
/// is deterministic regardless of the policy).
fn blocked_threads(nexts: &[ThreadNext]) -> Vec<Tid> {
    let mut blocked = Vec::new();
    for (tid, next) in nexts.iter().enumerate() {
        if let ThreadNext::Next(Label::Recv { blocking: true, .. }) = next {
            blocked.push(tid);
        }
    }
    blocked
}

/// The discrete-event `next_P(G)` policy of the time-intervals extension. It fixes a
/// deterministic insertion order using lower bounds from the hard temporal constraints.
/// Those bounds can be strictly below every full feasible schedule: eager competitor
/// constraints can raise another process's clock. Also, a receive ranked by one source
/// can choose a later source in its forward fork. Thus this ordering alone does not prove
/// that all earlier-arriving sends are present, or that timed pruning is complete.
///
/// The order is a pure function of `g` (not of `priorities`): ties break by `(tid, idx)`, so
/// `≤_G` is well defined and the whole search is priority-invariant by construction. Under the
/// T2 predicate `g` is eager-feasible on entry (every graph reaching a Visit is gated feasible —
/// T2_PLAN §5), so [`earliest_times`](crate::time::earliest_times) returns `Some`. Under the
/// zombie regime (T2_ORACLE_SPEC §2.1) infeasible graphs ARE visited; `earliest_times = None`
/// then drops every LB to 0 and phase B's keys to the ∞ case, which keeps the policy a
/// deterministic *total* function of `g` — the only property `next_P` needs (§4.3 (i)–(iii)).
///
/// Two phases:
/// * **A (drain):** among addable threads whose next is *not* a blocking receive
///   (send / error / nondet / non-blocking receive), pick the minimum lower-bound time `LB`.
///   A send's `LB = Occ_lb + window.lo` (its earliest arrival); the clock-neutral events have
///   `LB = Occ_lb`. Never wake a blocking receive while any such event remains.
/// * **B (wake):** when no non-recv is addable, wake the addable blocking receive with the
///   minimum `fire_lb = max(Occ_lb, min over consistent unread matching sources S of avail_lb(S))`.
///   A receive that is addable (a matching unread send exists) but has *no consistent* source —
///   the p2p-overtaking corner — cannot fire; it sorts *after* every can-fire receive (design
///   note below) and, if picked, is added and dies in `visit_recv`, exactly as the untimed
///   policy would have it (matching T1: such a graph has no terminal here, not a blocked one).
///
/// Here `Occ_lb(tid)` is the `fire`-LB of the last blocking receive currently on thread `tid`
/// (else 0). Candidate `LB`s are computed for the *not-yet-added* next event from the current
/// graph's `earliest_times` plus the candidate's own window/Occ.
///
/// Note on non-blocking receives: they are drained in phase A by `LB = Occ_lb`, *not* deferred
/// to the end. Deferring them (to shrink later revisits' `Deleted` sets — the naive fix for the
/// C5 gap below) is **unsound**: a non-blocking receive that po-precedes a send strands that
/// send, so an early-time send is absent when a blocking receive wakes and its realizable read
/// is lost (fuzz case 260). See the report's "known limitation".
///
/// Design note (undetermined by the paper/notes — fixed here): the `fire_lb` of a blocking
/// receive with an empty consistent-source set is undefined (`min` of ∅). We treat it as `+∞`
/// so it is woken only when no can-fire receive exists; this is the choice that reproduces the
/// untimed terminal set (a permanently-unreadable receive is added-and-dies, never a spurious
/// blocked terminal).
fn pick_des(
    g: &ExecutionGraph,
    nexts: &[ThreadNext],
    mailbox_time: bool,
    supplied_read: Option<&crate::graph::Marks>,
    unread: Option<&[usize]>,
) -> NextStep {
    // `None` only on an eager-infeasible `g`: every Visit the T2-predicate explorer reaches is
    // gated feasible, so there `Some`; its hard-only LBs may still be loose. The zombie regime visits
    // infeasible graphs too; there the LBs fall back to 0 and the policy stays a deterministic
    // total function of `g` — the only property `next_P` needs.
    let earliest = if mailbox_time {
        crate::time::earliest_mailbox_times(g)
    } else {
        crate::time::earliest_times(g)
    };

    // Occ_lb(tid): the fire-LB of the last blocking receive currently on thread `tid`, else 0.
    // The next (not-yet-added) event of `tid` inherits this clock; a send adds its window.lo.
    let occ_lb = |tid: Tid| -> i64 {
        let len = g.thread_len(tid);
        for idx in (0..len).rev() {
            let e = EventId::new(tid, idx);
            if g.label(e).blocking() == Some(true) || g.label(e).is_timed_recv() {
                return earliest.as_ref().and_then(|es| es.fire_lb(e)).unwrap_or(0);
            }
        }
        0
    };

    // Phase A: minimum-LB non-(blocking-recv) addable event. Tie: (LB, tid).
    let mut best_a: Option<(i64, Tid)> = None;
    for (tid, next) in nexts.iter().enumerate() {
        let ThreadNext::Next(label) = next else {
            continue;
        };
        if matches!(label, Label::Recv { blocking: true, .. }) {
            continue; // phase B
        }
        // Send / error / nondet / non-blocking recv are always addable.
        debug_assert!(addable(g, tid, label));
        let lb = match label {
            Label::Send { window, .. } => occ_lb(tid).saturating_add(window.lo() as i64),
            _ => occ_lb(tid), // clock-neutral: nondet / error / non-blocking recv
        };
        if best_a.is_none_or(|(blb, btid)| (lb, tid) < (blb, btid)) {
            best_a = Some((lb, tid));
        }
    }
    if let Some((_, tid)) = best_a {
        return NextStep::Event {
            tid,
            label: nexts[tid]
                .label()
                .expect("phase-A winner has a next")
                .clone(),
        };
    }

    // Phase B: wake the earliest-firing addable blocking receive. Sort key
    // `(has_no_source, fire_value, tid)`: can-fire receives (has_no_source = false) first, then
    // by fire_lb, then tid; a no-consistent-source receive (has_no_source = true) is the ∞ case.
    let mut best_b: Option<(bool, i64, Tid)> = None;
    for (tid, next) in nexts.iter().enumerate() {
        let ThreadNext::Next(label) = next else {
            continue;
        };
        if label.blocking() != Some(true) {
            continue;
        }
        let addable = supplied_read.map_or_else(
            || addable(g, tid, label),
            |read| addable_with_counts(g, tid, label, read, unread),
        );
        if !addable {
            continue;
        }
        let sources = crate::time::consistent_sources(g, tid, label);
        let key = match sources
            .iter()
            .filter_map(|&s| earliest.as_ref().and_then(|es| es.avail_lb(s)))
            .min()
        {
            Some(min_avail) => (false, occ_lb(tid).max(min_avail), tid),
            None => (true, occ_lb(tid), tid), // ∞: no consistent source (add-and-die corner)
        };
        if best_b.is_none_or(|b| key < b) {
            best_b = Some(key);
        }
    }
    if let Some((_, _, tid)) = best_b {
        return NextStep::Event {
            tid,
            label: nexts[tid]
                .label()
                .expect("phase-B winner has a next")
                .clone(),
        };
    }

    // Nothing addable: a terminal (full if no blocked thread, else blocked).
    NextStep::Terminal {
        blocked: blocked_threads(nexts),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::{Label, Model, Pred};

    /// Table-driven mock: `nexts[i]` is thread `i`'s next event, independent of the
    /// trace. Enough to unit-test addability without coroutines.
    struct Mock {
        nexts: Vec<ThreadNext>,
    }
    impl Program for Mock {
        fn num_threads(&self) -> usize {
            self.nexts.len()
        }
        fn next(&self, _traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.nexts.clone()
        }
    }

    fn send(dst: Tid, v: &str) -> Label {
        Label::send(Model::P2p, dst, v)
    }

    #[test]
    fn supplied_read_marks_preserve_priority_and_des_decisions() {
        fn assert_same(left: NextStep, right: NextStep) {
            match (left, right) {
                (
                    NextStep::Event { tid: lt, label: ll },
                    NextStep::Event { tid: rt, label: rl },
                ) => {
                    assert_eq!(lt, rt);
                    assert_eq!(ll, rl);
                }
                (NextStep::Terminal { blocked: left }, NextStep::Terminal { blocked: right }) => {
                    assert_eq!(left, right)
                }
                _ => panic!("supplied marks changed terminal/event classification"),
            }
        }
        let mut g = ExecutionGraph::new();
        let a = g.add_event(0, Label::send(Model::Asyn, 2, "a"));
        let b = g.add_event(1, Label::send(Model::Asyn, 2, "b"));
        let r = g.add_event(2, Label::recv(Pred::any()));
        for source in [a, b] {
            g.set_rf(r, Some(source));
            let mut read = crate::graph::PooledMarks::take();
            crate::consistency::mark_read_sources(&g, None, &mut read);
            let unread: Vec<_> = (0..3)
                .map(|tid| {
                    g.iter_sends()
                        .filter(|&s| g.label(s).dst() == Some(tid) && !read.contains(s))
                        .count()
                })
                .collect();
            for next in [
                Label::recv(Pred::any()),
                Label::recv(Pred::eq("a")),
                Label::recv(Pred::eq("b")),
                Label::recv(Pred::eq("missing")),
                Label::recv(Pred::new("true", |_| false)),
                Label::recv(Pred::new("true", |_| true)),
                Label::recv_nb(Pred::any()),
            ] {
                let nexts = [
                    ThreadNext::Next(Label::recv(Pred::any())),
                    ThreadNext::Finished,
                    ThreadNext::Next(next),
                ];
                for priorities in [[0, 1, 2], [2, 1, 0]] {
                    for des in [false, true] {
                        assert_same(
                            pick_with_read_marks(
                                &g,
                                &nexts,
                                &priorities,
                                des,
                                false,
                                &read,
                                Some(&unread),
                            ),
                            pick_with_time_semantics(&g, &nexts, &priorities, des, false),
                        );
                        assert_same(
                            pick_with_read_marks(&g, &nexts, &priorities, des, false, &read, None),
                            pick_with_time_semantics(&g, &nexts, &priorities, des, false),
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn pooled_traces_remain_independent_across_nested_visits() {
        let mut g = ExecutionGraph::new();
        let source = g.add_event(0, send(1, "value"));
        let receive = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(receive, Some(source));
        let mut parent = pooled_traces_of(&g, 3);
        assert_eq!(*parent, traces_of(&g, 3));
        let mut child = g.clone();
        let nondet = child.add_event(2, Label::nondet(["chosen"]));
        child.set_nd(nondet, crate::intern::intern("chosen"));
        {
            let nested = pooled_traces_of(&child, 3);
            assert_eq!(*nested, traces_of(&child, 3));
            assert_eq!(*parent, traces_of(&g, 3));
        }
        parent[0].push(None);
        drop(parent);
        assert_eq!(*pooled_traces_of(&g, 3), traces_of(&g, 3));
        assert_eq!(*pooled_traces_of(&ExecutionGraph::new(), 1), vec![vec![]]);
    }

    #[test]
    fn send_is_always_addable() {
        let g = ExecutionGraph::new();
        assert!(addable(&g, 0, &send(1, "1")));
        assert!(addable(&g, 0, &Label::error("boom")));
    }

    #[test]
    fn blocking_recv_addable_only_with_matching_unread_send() {
        let mut g = ExecutionGraph::new();
        // No send yet: not addable.
        assert!(!addable(&g, 1, &Label::recv(Pred::any())));
        // A send to thread 1: now addable.
        g.add_event(0, send(1, "1"));
        assert!(addable(&g, 1, &Label::recv(Pred::any())));
        // Predicate is honoured: recv(x = "2") does not match a "1".
        assert!(!addable(&g, 1, &Label::recv(Pred::eq("2"))));
        // A send to a different thread does not help.
        assert!(!addable(&g, 2, &Label::recv(Pred::any())));
    }

    #[test]
    fn nonblocking_recv_is_always_addable() {
        let g = ExecutionGraph::new();
        assert!(addable(&g, 0, &Label::recv_nb(Pred::any())));
    }

    #[test]
    fn read_send_no_longer_helps_addability() {
        let mut g = ExecutionGraph::new();
        let s = g.add_event(0, send(1, "1"));
        let r = g.add_event(1, Label::recv(Pred::any()));
        g.set_rf(r, Some(s));
        // The only matching send is already read: a new blocking recv on 1 blocks.
        assert!(!addable(&g, 1, &Label::recv(Pred::any())));
    }

    #[test]
    fn priority_order_picks_first_addable() {
        let prog = Mock {
            nexts: vec![
                ThreadNext::Finished,
                ThreadNext::Next(send(2, "b")),
                ThreadNext::Next(send(2, "a")),
            ],
        };
        let g = ExecutionGraph::new();
        // Default order [0,1,2]: thread 0 finished, thread 1 is first addable.
        match next_step(&prog, &[0, 1, 2], &g) {
            NextStep::Event { tid, .. } => assert_eq!(tid, 1),
            NextStep::Terminal { .. } => panic!("expected an event"),
        }
        // Reordered [2,1,0]: thread 2 wins.
        match next_step(&prog, &[2, 1, 0], &g) {
            NextStep::Event { tid, .. } => assert_eq!(tid, 2),
            NextStep::Terminal { .. } => panic!("expected an event"),
        }
    }

    #[test]
    fn terminal_reports_blocked_threads() {
        // Thread 0 wants a message that will never come; thread 1 is finished.
        let prog = Mock {
            nexts: vec![
                ThreadNext::Next(Label::recv(Pred::any())),
                ThreadNext::Finished,
            ],
        };
        let g = ExecutionGraph::new();
        match next_step(&prog, &[0, 1], &g) {
            NextStep::Terminal { blocked } => assert_eq!(blocked, vec![0]),
            NextStep::Event { .. } => panic!("expected terminal"),
        }
    }

    #[test]
    fn terminal_all_finished_is_full() {
        let prog = Mock {
            nexts: vec![ThreadNext::Finished, ThreadNext::Finished],
        };
        let g = ExecutionGraph::new();
        match next_step(&prog, &[0, 1], &g) {
            NextStep::Terminal { blocked } => assert!(blocked.is_empty()),
            NextStep::Event { .. } => panic!("expected terminal"),
        }
    }

    /// Rescheduling (Example 4.1): with thread 2 (the receiver) first in priority but no
    /// message, the scheduler skips it and picks a sender; once a send exists, the
    /// receiver becomes addable on the same priority order.
    #[test]
    fn rescheduling_skips_blocked_receiver_then_unblocks() {
        let prog = Mock {
            nexts: vec![
                ThreadNext::Next(send(2, "1")),
                ThreadNext::Next(send(2, "2")),
                ThreadNext::Next(Label::recv(Pred::any())),
            ],
        };
        let mut g = ExecutionGraph::new();
        // Receiver (2) has top priority but no message: a sender is chosen instead.
        match next_step(&prog, &[2, 0, 1], &g) {
            NextStep::Event { tid, .. } => assert_ne!(tid, 2),
            NextStep::Terminal { .. } => panic!("expected an event"),
        }
        // After a matching send appears, the same priority order now schedules 2.
        g.add_event(0, send(2, "1"));
        match next_step(&prog, &[2, 0, 1], &g) {
            NextStep::Event { tid, .. } => assert_eq!(tid, 2),
            NextStep::Terminal { .. } => panic!("expected an event"),
        }
    }
}
