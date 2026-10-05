//! Independent preservation tests for timing cuts certified by immutable graph cores.
//! The authoritative oracle is original MUST plus terminal filtering; the small
//! finite-window graphs are also checked by the independent delay enumerator.

mod common;

use std::collections::BTreeSet;
use std::sync::Mutex;

use common::{permutations, SeqProgram};
use must::{
    consistent, explore, Config, CountingObserver, Execution, ExecutionGraph, ExecutionKind, Label,
    Model, Observer, Pred, Program, SourceOrder, ThreadNext, Val, Window,
};

#[derive(Default)]
struct Exact {
    keys: Mutex<BTreeSet<String>>,
}

impl Observer for Exact {
    fn on_execution(&self, execution: &Execution, kind: ExecutionKind) {
        assert_eq!(
            common::time_feasible_ref(execution.graph(), &mut 10_000),
            Some(true),
            "reported graph must pass the independent finite-delay check without skipping"
        );
        assert!(
            self.keys
                .lock()
                .unwrap()
                .insert(format!("{kind:?}:{}", execution.canonical_key())),
            "duplicate terminal graph"
        );
    }

    fn on_execution_filtered(&self, execution: &Execution, _kind: ExecutionKind) {
        assert_eq!(
            common::time_feasible_ref(execution.graph(), &mut 10_000),
            Some(false),
            "filtered graph must fail the independent finite-delay check without skipping"
        );
    }
}

fn send(model: Model, dst: usize, payload: &str, lo: u64, hi: u64) -> Label {
    Label::send_within(model, dst, payload, Window::new(lo, hi))
}

fn matrix<P: Program + Clone + Sync>(program: &P, expected_count: Option<usize>) -> usize {
    let mut prunes = 0;
    for priorities in permutations(program.num_threads()) {
        let base = Config::default()
            .collect_errors()
            .with_priorities(priorities.clone());
        let reference = Exact::default();
        explore(
            || program.clone(),
            &reference,
            base.clone().with_time_filter(),
        );
        let wanted = reference.keys.into_inner().unwrap();
        if let Some(expected_count) = expected_count {
            assert_eq!(wanted.len(), expected_count);
        }
        for source_order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
            let ordered = base.clone().with_source_order(source_order);
            for config in [
                ordered.clone().with_time_filter(),
                ordered.clone().with_certified_time(),
                ordered.clone().with_time_filter().with_certified_time(),
                ordered
                    .with_certified_time()
                    .with_certified_time_budget(0, 0),
            ] {
                let observed = (CountingObserver::new(), Exact::default());
                explore(|| program.clone(), &observed, config);
                assert_eq!(
                    observed.1.keys.into_inner().unwrap(),
                    wanted,
                    "priorities={priorities:?} source_order={source_order:?}"
                );
                prunes += observed.0.time_certificate_prunes();
            }
        }
    }
    prunes
}

fn repairing_send_after_extra() -> SeqProgram {
    let s = |dst, payload, lo, hi| send(Model::Asyn, dst, payload, lo, hi);
    SeqProgram::new(vec![
        vec![s(0, "B", 20, 20), Label::recv(Pred::any())],
        vec![
            s(1, "w", 1, 20),
            Label::recv(Pred::eq("w")),
            s(0, "c", 1, 1),
            s(1, "m1", 1, 1),
            s(1, "m2", 1, 1),
            Label::recv(Pred::any()),
            s(0, "extra", 1, 1),
        ],
        vec![s(2, "g", 9, 9), Label::recv(Pred::eq("g")), s(1, "s", 1, 1)],
    ])
}

#[test]
fn future_repair_survives_all_original_priority_orders() {
    // Current T2's forward-closure gate loses one of these five graphs. A frozen
    // core must not accidentally freeze an ordinary, still-revisitable holder.
    let prunes = matrix(&repairing_send_after_extra(), Some(5));
    assert!(
        prunes > 0,
        "this supported case must exercise real certified pruning"
    );
}

#[test]
fn nonminimum_nondeterminism_freezes_its_causal_past() {
    for wire in [Model::Asyn, Model::P2p] {
        let program = SeqProgram::new(vec![
            vec![
                send(Model::Asyn, 0, "late", 5, 5),
                send(Model::Asyn, 0, "early", 1, 1),
                Label::recv(Pred::any()),
                Label::nondet(["a", "b"]),
                send(wire, 1, "done", 1, 2),
            ],
            vec![Label::recv(Pred::eq("done"))],
        ]);
        matrix(&program, Some(2));
    }
}

#[test]
fn positive_nonblocking_receive_freezes_source_dependencies() {
    for wire in [Model::Asyn, Model::P2p] {
        let program = SeqProgram::new(vec![
            vec![
                send(Model::Asyn, 0, "late", 5, 5),
                send(Model::Asyn, 0, "early", 1, 1),
                Label::recv(Pred::any()),
                send(wire, 1, "notice", 1, 2),
            ],
            vec![Label::recv_nb(Pred::eq("notice"))],
        ]);
        matrix(&program, Some(2));
    }
}

#[test]
fn smaller_asynchronous_ancestor_and_mixed_fifo_channels() {
    for wire in [Model::Asyn, Model::P2p] {
        let program = SeqProgram::new(vec![
            vec![
                send(Model::Asyn, 0, "timer", 1, 1),
                Label::recv(Pred::any()),
                send(wire, 1, "reply", 1, 2),
            ],
            vec![send(wire, 0, "late", 5, 5), Label::recv(Pred::eq("reply"))],
            vec![send(wire, 0, "later", 8, 8)],
        ]);
        matrix(&program, Some(1));
    }
}

#[test]
fn equal_arrivals_and_fifo_availability_keep_both_legal_choices() {
    for wire in [Model::Asyn, Model::P2p] {
        let program = SeqProgram::new(vec![
            vec![send(wire, 1, "a", 1, 3), send(wire, 1, "b", 2, 2)],
            vec![Label::recv(Pred::any()), Label::recv(Pred::any())],
        ]);
        matrix(&program, Some(if wire == Model::Asyn { 2 } else { 1 }));
    }
}

#[test]
fn mixed_model_preservation_with_two_workers() {
    let program = SeqProgram::new(vec![
        vec![
            send(Model::Asyn, 0, "late", 5, 5),
            send(Model::Asyn, 0, "early", 1, 1),
            Label::recv(Pred::any()),
            Label::nondet(["a", "b"]),
            send(Model::P2p, 1, "notice", 1, 1),
        ],
        vec![Label::recv_nb(Pred::eq("notice"))],
    ]);
    let reference = Exact::default();
    explore(
        || program.clone(),
        &reference,
        Config::default().collect_errors().with_time_filter(),
    );
    let wanted = reference.keys.into_inner().unwrap();
    assert_eq!(wanted.len(), 4);
    for source_order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
        let observed = Exact::default();
        explore(
            || program.clone(),
            &observed,
            Config::default()
                .collect_errors()
                .with_source_order(source_order)
                .with_certified_time()
                .with_threads(2),
        );
        assert_eq!(observed.keys.into_inner().unwrap(), wanted);
    }
}

#[test]
fn earlier_consumer_excludes_a_smaller_fifo_blocker() {
    // The first self-send is smaller than the old holder but already consumed.
    // Freezing the second receive from that source would erase its valid repair.
    for wire in [Model::Asyn, Model::P2p] {
        let program = SeqProgram::new(vec![
            vec![
                send(wire, 0, "consumed", 1, 1),
                send(wire, 0, "old", 3, 3),
                Label::recv(Pred::eq("consumed")),
                Label::recv(Pred::any()),
            ],
            vec![
                send(Model::Asyn, 1, "wake", 1, 1),
                Label::recv(Pred::eq("wake")),
                send(wire, 0, "repair", 1, 1),
            ],
        ]);
        matrix(&program, Some(1));
    }
}

#[test]
fn later_positive_poll_does_not_hide_a_smaller_blocker_from_previous() {
    // A later positive NB receive holds m in the complete graph. The original
    // canonical Previous(r) excludes that poll, where m is available again.
    for wire in [Model::Asyn, Model::P2p] {
        let program = SeqProgram::new(vec![
            vec![
                send(wire, 0, "m", 2, 2),
                send(Model::Asyn, 0, "held", 2, 2),
                Label::recv(Pred::any()),
                Label::recv_nb(Pred::eq("m")),
            ],
            vec![
                send(Model::Asyn, 1, "wake", 1, 1),
                Label::recv(Pred::eq("wake")),
                send(Model::Asyn, 0, "future", 1, 1),
            ],
        ]);
        // At the equal arrival instant, polling may precede m's delivery or
        // consume it. Together with r consuming m, that gives five graphs.
        matrix(&program, Some(5));
    }
}

#[test]
fn fifo_blocker_trials_require_full_local_consistency() {
    // A tempting smaller P2p source m is unavailable while its matching
    // predecessor p is unread. A different sender's held source is consistent.
    let mut graph = ExecutionGraph::new();
    let p = graph.add_event(0, send(Model::P2p, 2, "p", 5, 5));
    let m = graph.add_event(0, send(Model::P2p, 2, "m", 1, 1));
    let held = graph.add_event(1, send(Model::Asyn, 2, "held", 2, 2));
    let r = graph.add_event(2, Label::recv(Pred::any()));
    graph.set_rf(r, Some(held));
    assert!(consistent(&graph));
    graph.set_rf(r, Some(m));
    assert!(!consistent(&graph), "m skips an unread FIFO predecessor");
    graph.set_rf(r, Some(p));
    assert!(consistent(&graph));

    matrix(
        &SeqProgram::new(vec![
            vec![
                send(Model::P2p, 2, "p", 5, 5),
                send(Model::P2p, 2, "m", 1, 1),
            ],
            vec![send(Model::Asyn, 2, "held", 2, 2)],
            vec![Label::recv(Pred::any())],
        ]),
        Some(1),
    );

    // Making an old P2p source unread cannot introduce a new unread-predecessor
    // conflict at an earlier read: that proposed original host already violates
    // the receive-order clause, before the rewrite is considered.
    let mut graph = ExecutionGraph::new();
    let smaller = graph.add_event(0, send(Model::Asyn, 2, "smaller", 1, 1));
    let old = graph.add_event(1, send(Model::P2p, 2, "old", 1, 1));
    let later = graph.add_event(1, send(Model::P2p, 2, "later", 1, 1));
    let earlier_read = graph.add_event(2, Label::recv(Pred::any()));
    graph.set_rf(earlier_read, Some(later));
    let r = graph.add_event(2, Label::recv(Pred::any()));
    graph.set_rf(r, Some(old));
    assert!(!consistent(&graph), "the original host is already invalid");
    graph.set_rf(r, Some(smaller));
    assert!(!consistent(&graph), "the trial still skips unread old");
}

#[test]
fn mutually_supporting_blockers_preserve_the_exact_terminal_set() {
    // The initial bottom poll stays mutable and prevents an initial-prefix
    // certificate from automatically protecting the two cross-thread sends.
    // When both receives hold T2's larger sources, each smaller blocker belongs
    // to the OTHER receive's causal past. The mutual-support proof must consider
    // a revisit that deletes both receives, not assume independent induction.
    for wire in [Model::Asyn, Model::P2p] {
        let program = SeqProgram::new(vec![
            vec![
                Label::recv_nb(Pred::eq("absent")),
                send(wire, 1, "m0", 1, 1),
                Label::recv(Pred::any()),
            ],
            vec![send(wire, 0, "m1", 1, 1), Label::recv(Pred::any())],
            vec![
                send(Model::Asyn, 0, "u0", 2, 2),
                send(Model::Asyn, 1, "u1", 2, 2),
            ],
        ]);
        matrix(&program, Some(1));
    }
}

#[test]
fn untimed_self_send_order_matches_brute_force_for_every_message_model() {
    #[derive(Default)]
    struct Untimed(Mutex<BTreeSet<String>>);
    impl Observer for Untimed {
        fn on_execution(&self, execution: &Execution, kind: ExecutionKind) {
            assert!(
                self.0
                    .lock()
                    .unwrap()
                    .insert(format!("{kind:?}:{}", execution.canonical_key())),
                "source-order change introduced duplicate untimed terminals"
            );
        }
    }
    for remote in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
        for local in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
            let program = SeqProgram::new(vec![
                vec![Label::send(remote, 1, "a"), Label::send(remote, 1, "b")],
                vec![
                    Label::recv_nb(Pred::eq("absent")),
                    Label::send(local, 1, "self"),
                    Label::recv(Pred::any()),
                    Label::nondet(["a", "b"]),
                    Label::recv_nb(Pred::any()),
                    Label::recv(Pred::eq("b")),
                ],
            ]);
            // Independent forward BFS enumerates every enabled process/choice;
            // it uses no MUST canonical condition and no timing pruning.
            let states = common::all_states(&ExecutionGraph::new(), &program);
            assert!(states.len() < 10_000, "explicit finite brute-force bound");
            let wanted: BTreeSet<_> = states
                .into_iter()
                .filter_map(|graph| {
                    let next = program.next(&must::traces_of(&graph, program.num_threads()));
                    match must::scheduler::pick(&graph, &next, &[0, 1], false) {
                        must::scheduler::NextStep::Terminal { blocked } => {
                            let kind = if blocked.is_empty() {
                                ExecutionKind::Full
                            } else {
                                ExecutionKind::Blocked
                            };
                            Some(format!("{kind:?}:{}", graph.canonical_key()))
                        }
                        _ => None,
                    }
                })
                .collect();
            assert!(!wanted.is_empty());
            for priorities in permutations(2) {
                for source_order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
                    let observed = Untimed::default();
                    explore(
                        || program.clone(),
                        &observed,
                        Config::default()
                            .collect_errors()
                            .with_priorities(priorities.clone())
                            .with_source_order(source_order),
                    );
                    assert_eq!(observed.0.into_inner().unwrap(), wanted,
                        "remote={remote:?} local={local:?} priorities={priorities:?} order={source_order:?}");
                }
            }
        }
    }
}

#[test]
fn an_unfinished_empty_thread_can_supply_the_first_valid_repair() {
    // Priority T0 reaches an impossible late read while T1 still has no event.
    // The empty tail is no certificate: T1's immediate send owns the valid read.
    let program = SeqProgram::new(vec![
        vec![
            send(Model::Asyn, 0, "late", 3, 3),
            send(Model::Asyn, 0, "early", 1, 1),
            Label::recv(Pred::any()),
        ],
        vec![send(Model::Asyn, 0, "repair", 0, 0)],
    ]);
    matrix(&program, Some(1));
}

#[derive(Clone)]
struct RewoundSender {
    nonblocking: bool,
    cyclic_dependency: bool,
}

impl Program for RewoundSender {
    fn num_threads(&self) -> usize {
        3
    }

    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..3)
            .map(|tid| self.next_thread(tid, &traces[tid]))
            .collect()
    }

    fn next_thread(&self, tid: usize, trace: &[Option<Val>]) -> ThreadNext {
        let s = |dst, value, lo, hi| send(Model::Asyn, dst, value, lo, hi);
        if tid == 0 {
            return match trace.len() {
                0 => ThreadNext::Next(if self.nonblocking {
                    Label::recv_nb(Pred::eq("good"))
                } else {
                    Label::recv(Pred::any())
                }),
                1 if trace[0] == Some(must::intern::intern("good")) => {
                    ThreadNext::Next(s(1, "repair", 0, 0))
                }
                _ => ThreadNext::Finished,
            };
        }
        let labels = if tid == 1 {
            let mut labels = vec![
                s(1, "late", 3, 3),
                s(1, "early", 1, 1),
                Label::recv(Pred::any()),
            ];
            if self.cyclic_dependency {
                labels.push(s(2, "wake", 0, 0));
            }
            labels
        } else if self.cyclic_dependency {
            vec![
                s(0, "bad", 1, 4),
                Label::recv(Pred::eq("wake")),
                s(0, "good", 0, 0),
            ]
        } else if self.nonblocking {
            vec![
                s(2, "wake", 0, 0),
                Label::recv(Pred::eq("wake")),
                s(0, "good", 0, 0),
            ]
        } else {
            vec![
                s(0, "bad", 1, 4),
                s(2, "wake", 1, 1),
                Label::recv(Pred::eq("wake")),
                s(0, "good", 0, 0),
            ]
        };
        labels
            .get(trace.len())
            .cloned()
            .map_or(ThreadNext::Finished, ThreadNext::Next)
    }
    // No future alphabet is provided. All decisions use actual local traces.
}

#[test]
fn first_repair_can_rewind_a_finished_sender_and_enable_a_second_repair() {
    // T0 is finished after "bad", but a first repair to "good" enables a send
    // that can repair T1. Treating currently finished threads as permanently
    // finished would lose this valid graph. The first source's causal core is
    // feasible, so the first-alteration certificate must decline the cut.
    matrix(
        &RewoundSender {
            nonblocking: false,
            cyclic_dependency: false,
        },
        Some(3),
    );
}

#[test]
fn nonblocking_bottom_can_rewind_a_finished_sender() {
    matrix(
        &RewoundSender {
            nonblocking: true,
            cyclic_dependency: false,
        },
        Some(2),
    );
}

#[test]
fn a_causal_cycle_cannot_be_used_as_a_second_repair() {
    // Here the first repairing send inherits T1's old receive. Its new reply
    // cannot subsequently rewrite that ancestor: doing so would close a cycle.
    matrix(
        &RewoundSender {
            nonblocking: false,
            cyclic_dependency: true,
        },
        Some(2),
    );
}

#[test]
fn six_process_feedback_preserves_every_acyclic_timed_terminal() {
    #[derive(Clone)]
    struct NoFuture(SeqProgram);
    impl Program for NoFuture {
        fn num_threads(&self) -> usize {
            self.0.num_threads()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.0.next(traces)
        }
    }
    let program = NoFuture(SeqProgram::new(
        (0..6)
            .map(|tid| {
                vec![
                    send(Model::Asyn, tid, "late", 2, 2),
                    send(Model::Asyn, tid, "early", 1, 1),
                    Label::recv(Pred::any()),
                    send(Model::Asyn, (tid + 1) % 6, "relay", 0, 0),
                ]
            })
            .collect(),
    ));
    // Each receive chooses its early timer or the neighbour's relay; the single
    // all-relay cycle is inconsistent, leaving 2^6 - 1 valid terminal graphs.
    for priorities in [(0..6).collect::<Vec<_>>(), (0..6).rev().collect()] {
        let reference = Exact::default();
        let base = Config::default()
            .collect_errors()
            .with_priorities(priorities);
        explore(
            || program.clone(),
            &reference,
            base.clone().with_time_filter(),
        );
        let wanted = reference.keys.into_inner().unwrap();
        assert_eq!(wanted.len(), 63);
        for source_order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
            for config in [
                base.clone().with_certified_time(),
                base.clone().with_time_filter().with_certified_time(),
            ] {
                let observed = Exact::default();
                explore(
                    || program.clone(),
                    &observed,
                    config.with_source_order(source_order),
                );
                assert_eq!(observed.keys.into_inner().unwrap(), wanted);
            }
        }
    }
}
