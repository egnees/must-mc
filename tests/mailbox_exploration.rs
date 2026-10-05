//! New timing must preserve exactly original MUST's terminal graphs after verification.
//! The reference below runs without any timed scheduling/filtering/pruning and applies
//! the new verifier afterwards, including to blocked and erroneous executions.
mod common;

use common::SeqProgram;
use must::{
    check_mailbox, explore, Config, CountingObserver, DeadBranchDetector, ExecutionCollector,
    Label, Model, Pred, Program, SourceOrder, ThreadNext, Val, Window,
};
use std::collections::BTreeSet;

fn keys(collector: &ExecutionCollector, filter: bool) -> BTreeSet<(u8, String)> {
    let mut result = BTreeSet::new();
    for (kind, executions) in [collector.full(), collector.blocked(), collector.errors()]
        .into_iter()
        .enumerate()
    {
        for execution in executions {
            if filter && !check_mailbox(execution.graph()).is_feasible() {
                continue;
            }
            assert!(
                result.insert((kind as u8, execution.canonical_key())),
                "duplicate terminal"
            );
        }
    }
    result
}

fn verify<P: Program + Clone + Sync>(program: &P, parallel: bool) {
    let original = ExecutionCollector::new();
    explore(
        || program.clone(),
        &original,
        Config::default().collect_errors(),
    );
    let reference = keys(&original, true);
    for order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
        for des in [false, true] {
            let base = Config::default()
                .collect_errors()
                .with_mailbox_time()
                .with_source_order(order);
            let base = if des {
                base.with_time_zombie()
            } else {
                base.with_time_filter()
            };
            for budget in [None, Some((0, 0)), Some((128, 64))] {
                let config = match budget {
                    None => base.clone(),
                    Some((states, events)) => {
                        base.clone().with_certified_time_budget(states, events)
                    }
                };
                for threads in if parallel { vec![1, 2] } else { vec![1] } {
                    let collector = ExecutionCollector::new();
                    explore(
                        || program.clone(),
                        &collector,
                        config.clone().with_threads(threads),
                    );
                    assert_eq!(
                        reference,
                        keys(&collector, false),
                        "order={order:?}, des={des}, budget={budget:?}, threads={threads}"
                    );
                }
            }
        }
    }
}

fn send(model: Model, dst: usize, value: &str, delay: u64) -> Label {
    Label::send_within(model, dst, value, Window::new(delay, delay))
}
fn timeout(value: &str, delay: u64) -> Label {
    Label::recv_timeout_timed(Pred::eq(value), Window::new(delay, delay))
}

#[test]
fn all_models_preserve_full_blocked_error_sets_and_parallel() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        // Empty timeout enables a same-time future send; polling reads can instead
        // force an early source. A final blocking suffix exercises blocked terminals.
        verify(
            &SeqProgram::new(vec![
                vec![
                    timeout("reply", 0),
                    send(model, 1, "request", 0),
                    Label::recv(Pred::eq("reply")),
                ],
                vec![
                    Label::recv_poll_timed(Pred::eq("request"), Window::new(0, 1)),
                    send(model, 0, "reply", 1),
                    Label::recv(Pred::eq("absent")),
                ],
            ]),
            true,
        );
        verify(&DataDependent(model), true);
    }
}

#[derive(Clone)]
struct DataDependent(Model);
impl Program for DataDependent {
    fn num_threads(&self) -> usize {
        3
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..3)
            .map(|tid| {
                let labels = match tid {
                    0 => vec![send(self.0, 1, "red", 1), send(self.0, 1, "blue", 2)],
                    1 => {
                        let first = Label::recv_timeout_timed(Pred::any(), Window::new(0, 2));
                        match traces[1].first().copied().flatten() {
                            Some(v) if v == "red".into() => vec![first, send(self.0, 2, "ok", 0)],
                            Some(_) => {
                                vec![first, send(self.0, 2, "other", 0), Label::error("blue")]
                            }
                            None => vec![first, send(self.0, 2, "empty", 0)],
                        }
                    }
                    _ => vec![
                        Label::recv_timeout_timed(Pred::any(), Window::new(0, 4)),
                        Label::recv(Pred::eq("never")),
                    ],
                };
                labels
                    .get(traces[tid].len())
                    .cloned()
                    .map_or(ThreadNext::Finished, ThreadNext::Next)
            })
            .collect()
    }
}

#[test]
fn bounded_window_corpus_matches_erased_reference() {
    for model in [Model::Asyn, Model::P2p, Model::Mbox] {
        for code in 0..32u64 {
            let a = code % 3;
            let b = (code / 3) % 3;
            let window = Window::new(code % 2, 2);
            let receive = if code & 8 == 0 {
                Label::recv_timeout_timed(Pred::any(), window)
            } else {
                Label::recv_poll_timed(Pred::any(), window)
            };
            verify(
                &SeqProgram::new(vec![
                    vec![send(model, 1, "a", a), send(model, 1, "b", b)],
                    vec![receive, timeout("a", code % 2), send(model, 0, "reply", 0)],
                ]),
                false,
            );
        }
    }
}

#[test]
fn send_only_fifo_conflict_prunes_and_counts_the_examined_boundary() {
    let program = SeqProgram::new(vec![
        vec![send(Model::P2p, 1, "a", 10), send(Model::P2p, 1, "b", 1)],
        vec![],
    ]);
    let obs = (CountingObserver::new(), DeadBranchDetector::new());
    explore(
        || program.clone(),
        &obs,
        Config::default()
            .collect_errors()
            .with_mailbox_time()
            .with_time_filter()
            .with_certified_time(),
    );
    assert_eq!(
        obs.1.visits(),
        1,
        "the root proof drains both mandatory sends"
    );
    assert_eq!(obs.1.dead(), 1, "a cut is an examined barren vertex");
    assert_eq!(obs.0.full(), 0);
    assert_eq!(obs.0.filtered_full(), 0, "cut precedes any terminal filter");
}

#[test]
#[should_panic(expected = "explicit timeout or poll")]
fn mailbox_mode_rejects_abstract_nonblocking_receive() {
    let program = SeqProgram::new(vec![vec![Label::recv_nb(Pred::any())]]);
    explore(
        || program.clone(),
        &CountingObserver::new(),
        Config::default()
            .collect_errors()
            .with_time_filter()
            .with_mailbox_time(),
    );
}
