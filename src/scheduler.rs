//! The `next_P` scheduling policy.
//!
//! `next_P(G)` follows three rules: it never picks an event of a blocked thread; it never
//! adds a blocking receive when no matching message exists; and it reports a terminal
//! verdict only when nothing can be added. Addability is recomputed on the current graph
//! every call, so a receive is rescheduled the moment a matching send appears. There is no
//! explicit blocking event in the graph: a thread whose next event is a blocking receive
//! with no message is simply "blocked" at this graph, and unblocks when a send appears.

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

/// Extract each thread's trace: one value per event in po, `Some(v)` for a receive that
/// read value `v`, `None` for a send/error or a receive that read nothing.
pub fn traces_of(g: &ExecutionGraph, num_threads: usize) -> Vec<Vec<Option<Val>>> {
    let mut traces = vec![Vec::new(); num_threads];
    for (tid, trace) in traces.iter_mut().enumerate() {
        let len = g.thread_len(tid);
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
    traces
}

/// Whether thread `tid`'s next event `label` can be added to `g` right now.
///
/// Sends, errors, and non-blocking receives are always addable; a blocking receive is
/// addable only when some unread send matches its predicate and destination.
fn addable(g: &ExecutionGraph, tid: Tid, label: &Label) -> bool {
    match label {
        Label::Send { .. } | Label::Error { .. } => true,
        // A nondet choice is always addable; only blocking receives are ever held back.
        Label::Nondet { .. } => true,
        // A non-blocking receive can always read nothing, so it is always addable.
        Label::Recv {
            blocking: false, ..
        } => true,
        Label::Recv {
            blocking: true,
            pred,
        } => g.unread_sends().iter().any(|&s| {
            let lbl = g.label(s);
            lbl.dst() == Some(tid) && lbl.payload().is_some_and(|v| pred.test_sym(v))
        }),
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
    pick(g, &nexts, priorities)
}

/// The `next_P(G)` decision given the per-thread next events `nexts` already computed:
/// the first addable thread in `priorities` order, else a terminal verdict. Addability is
/// (re)checked against `g` here, not cached, so a receive unblocks the moment a matching
/// send appears.
pub fn pick(g: &ExecutionGraph, nexts: &[ThreadNext], priorities: &[Tid]) -> NextStep {
    for &tid in priorities {
        if let ThreadNext::Next(label) = &nexts[tid] {
            if addable(g, tid, label) {
                return NextStep::Event {
                    tid,
                    label: label.clone(),
                };
            }
        }
    }

    // Nothing addable: gather the threads parked on a blocking receive. In tid order so
    // the verdict is deterministic regardless of the priority permutation.
    let mut blocked = Vec::new();
    for (tid, next) in nexts.iter().enumerate() {
        if let ThreadNext::Next(Label::Recv { blocking: true, .. }) = next {
            blocked.push(tid);
        }
    }
    NextStep::Terminal { blocked }
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

    /// Rescheduling: with thread 2 (the receiver) first in priority but no
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
