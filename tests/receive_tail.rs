use std::sync::Mutex;

use must::explorer::receive_tail::{ReceiveTailBudget, ReceiveTailCertificate};
use must::{
    explore, Config, EventCountingObserver, Execution, ExecutionCollector, ExecutionGraph,
    ExecutionKind, Model, Observer, System, TraceLabel,
};

#[derive(Default)]
struct TailObserver {
    labels: Mutex<Vec<Vec<TraceLabel>>>,
    proofs: Mutex<Vec<(usize, usize)>>,
    drains: Mutex<Vec<bool>>,
    selective: Mutex<Vec<bool>>,
}

impl Observer for TailObserver {
    fn receive_tail_candidate(&self, _graph: &ExecutionGraph, _labels: &[TraceLabel]) -> bool {
        true
    }

    fn accept_receive_tail(&self, certificate: &ReceiveTailCertificate<'_>) -> bool {
        // This test observer checks only absence of *future* errors or annotations;
        // those facts follow directly from the certificate. Actual prefix failures
        // remain handled by ordinary terminal callbacks.
        assert!(certificate.pending_sends().iter().flatten().all(|&send| {
            certificate.graph().contains(send) && !certificate.graph().is_read(send)
        }));
        true
    }

    fn on_receive_tail_pruned(&self, certificate: &ReceiveTailCertificate<'_>) {
        self.selective
            .lock()
            .unwrap()
            .push(certificate.has_selective_receives());
        self.drains
            .lock()
            .unwrap()
            .push(certificate.drains_mailboxes());
        self.proofs.lock().unwrap().push((
            certificate.pending_sends().iter().map(Vec::len).sum(),
            certificate.states_checked(),
        ));
    }

    fn on_execution(&self, execution: &Execution, _kind: ExecutionKind) {
        self.labels
            .lock()
            .unwrap()
            .push(execution.labels().to_vec());
    }
}

fn silent_tail(identical: bool, model: Model) -> System {
    let mut system = System::new();
    system.add(move |ctx| async move {
        for value in if identical {
            ["a", "a", "a"]
        } else {
            ["a", "b", "c"]
        } {
            ctx.send(1, value, model);
        }
    });
    system.add(|ctx| async move {
        for _ in 0..3 {
            ctx.recv_any().await;
        }
    });
    system
}

fn enabled(threads: usize) -> Config {
    Config::default()
        .with_threads(threads)
        .with_receive_tail(ReceiveTailBudget::default())
}

#[test]
fn silent_families_are_separate_from_terminals_and_default_counts_are_unchanged() {
    for threads in [1, 12] {
        let plain = (EventCountingObserver::new(), TailObserver::default());
        explore(
            || silent_tail(false, Model::Asyn),
            &plain,
            Config::default().with_threads(threads),
        );
        assert_eq!(plain.0.full(), 6);
        assert_eq!(plain.0.receive_tails(), 0);

        let pruned = (EventCountingObserver::new(), TailObserver::default());
        explore(
            || silent_tail(false, Model::Asyn),
            &pruned,
            enabled(threads),
        );
        assert_eq!(pruned.0.receive_tails(), 1);
        assert_eq!(pruned.0.terminal(), 0);
        assert_eq!(pruned.0.errors(), 0);
        assert_eq!(pruned.1.proofs.lock().unwrap().len(), 1);
    }
}

#[test]
fn identical_payloads_share_proof_branches_but_retain_send_identities() {
    let observer = (EventCountingObserver::new(), TailObserver::default());
    explore(|| silent_tail(true, Model::Asyn), &observer, enabled(1));
    let proofs = observer.1.proofs.lock().unwrap();
    // Four receiver prefixes; the empty sender tail needs no query.
    // All three actual sends are retained.
    assert_eq!(&*proofs, &[(3, 4)]);
    assert_eq!(observer.0.receive_tails(), 1);
}

#[test]
fn exhausted_proof_budget_falls_back_to_complete_enumeration() {
    for budget in [
        ReceiveTailBudget {
            max_states: 0,
            max_pending_per_thread: 8,
        },
        ReceiveTailBudget {
            max_states: 1,
            max_pending_per_thread: 8,
        },
        ReceiveTailBudget {
            max_states: 8192,
            max_pending_per_thread: 1,
        },
    ] {
        let observer = (EventCountingObserver::new(), TailObserver::default());
        explore(
            || silent_tail(false, Model::Asyn),
            &observer,
            Config::default().with_receive_tail(budget),
        );
        assert_eq!(observer.0.receive_tails(), 0);
        assert_eq!(observer.0.full(), 6);
    }
}

#[test]
fn legacy_recording_observer_vetoes_omitting_its_executions() {
    let observer = (
        (EventCountingObserver::new(), TailObserver::default()),
        ExecutionCollector::new(),
    );
    explore(|| silent_tail(false, Model::Asyn), &observer, enabled(12));
    let ((counts, property), recordings) = &observer;
    assert_eq!(recordings.full_count(), 6);
    assert_eq!(counts.receive_tails(), 0);
    assert!(property.proofs.lock().unwrap().is_empty());
}

#[test]
fn a_second_receipt_error_or_annotation_is_not_mistaken_for_a_silent_tail() {
    for error in [false, true] {
        let observer = (EventCountingObserver::new(), TailObserver::default());
        explore(
            || {
                let mut system = System::new();
                system.add(|ctx| async move {
                    ctx.send(1, "first", Model::Asyn);
                    ctx.send(1, "second", Model::Asyn);
                });
                system.add(move |ctx| async move {
                    ctx.recv_any().await;
                    ctx.recv_any().await;
                    if error {
                        ctx.assert_that(false, "only after the second callback");
                    } else {
                        ctx.insert_label("DELIVER");
                    }
                });
                system
            },
            &observer,
            enabled(1),
        );
        assert_eq!(observer.0.receive_tails(), 0);
        if error {
            assert_eq!(observer.0.errors(), 1);
        } else {
            assert_eq!(observer.0.full(), 2);
            assert!(observer.1.labels.lock().unwrap().iter().all(|labels| {
                labels
                    .iter()
                    .any(|label| must::intern::resolve(label.value) == "DELIVER")
            }));
        }
    }
}

#[test]
fn late_send_after_two_quiet_receipts_can_still_revisit_an_old_receive() {
    let observer = (EventCountingObserver::new(), TailObserver::default());
    explore(
        || {
            let mut system = System::new();
            system.add(|ctx| async move {
                ctx.send(2, "old", Model::Asyn);
                ctx.send(1, "one", Model::Asyn);
                ctx.send(1, "two", Model::Asyn);
            });
            system.add(|ctx| async move {
                ctx.recv_any().await;
                ctx.recv_any().await;
                ctx.send(2, "new", Model::Asyn);
            });
            system.add(|ctx| async move {
                let value = ctx.recv_any().await;
                ctx.assert_that(value != "new", "backward revisit is required");
            });
            system
        },
        &observer,
        enabled(1).with_priorities(vec![0, 2, 1]),
    );
    assert_eq!(observer.0.receive_tails(), 0);
    assert_eq!(observer.0.errors(), 1);
}

#[test]
fn ancestor_send_revisits_survive_an_accepted_forward_tail() {
    let observer = (EventCountingObserver::new(), TailObserver::default());
    explore(
        || {
            let mut system = System::new();
            system.add(|ctx| async move {
                ctx.send(1, "old", Model::Asyn);
                ctx.send(2, "a", Model::Asyn);
                ctx.send(2, "b", Model::Asyn);
            });
            system.add(|ctx| async move {
                let value = ctx.recv_any().await;
                ctx.assert_that(value != "new", "ancestor send revisit survives");
                ctx.recv_any().await;
            });
            system.add(|ctx| async move {
                ctx.send(1, "new", Model::Asyn);
                ctx.recv_any().await;
                ctx.recv_any().await;
            });
            system
        },
        &observer,
        enabled(1),
    );
    // The forward suffix reads "new" only at the harmless second receive and
    // is omitted. The ancestor send can still revisit the *first* receive.
    assert!(observer.0.receive_tails() > 0);
    assert_eq!(observer.0.errors(), 1);
}

#[test]
fn fifo_and_timed_modes_do_not_use_asyn_tail_proofs() {
    for (model, config) in [
        (Model::P2p, enabled(1)),
        (Model::Asyn, enabled(1).collect_errors().with_time_filter()),
    ] {
        let observer = (EventCountingObserver::new(), TailObserver::default());
        explore(|| silent_tail(false, model), &observer, config);
        assert_eq!(observer.0.receive_tails(), 0);
        assert!(observer.0.full() > 0);
    }
}

#[test]
fn selective_tail_follows_matching_inputs_and_can_leave_rejected_duplicates() {
    for accept_all in [false, true] {
        let observer = (EventCountingObserver::new(), TailObserver::default());
        explore(
            || {
                let mut system = System::new();
                system.add(|ctx| async move {
                    ctx.send(1, "a", Model::Asyn);
                    ctx.send(1, "b", Model::Asyn);
                    ctx.send(1, "duplicate", Model::Asyn);
                });
                system.add(move |ctx| async move {
                    loop {
                        ctx.recv(move |value| accept_all || value != "duplicate")
                            .await;
                    }
                });
                system
            },
            &observer,
            enabled(1),
        );
        assert_eq!(observer.0.receive_tails(), 1);
        assert_eq!(observer.0.errors(), 0);
        assert_eq!(observer.0.terminal(), 0);
        assert_eq!(&*observer.1.drains.lock().unwrap(), &[accept_all]);
        assert_eq!(&*observer.1.selective.lock().unwrap(), &[true]);
    }
}

#[test]
fn finished_receivers_with_residual_mail_report_non_draining_certificates() {
    for receipts in [0, 1] {
        let observer = (EventCountingObserver::new(), TailObserver::default());
        explore(
            || {
                let mut system = System::new();
                system.add(|ctx| async move {
                    ctx.send(1, "a", Model::Asyn);
                    ctx.send(1, "b", Model::Asyn);
                    ctx.send(1, "c", Model::Asyn);
                    // Keep an addable receive even if process 1 starts Finished;
                    // an entirely terminal graph needs no tail certificate.
                    ctx.send(2, "live", Model::Asyn);
                });
                system.add(move |ctx| async move {
                    for _ in 0..receipts {
                        ctx.recv_any().await;
                    }
                });
                system.add(|ctx| async move {
                    ctx.recv_any().await;
                });
                system
            },
            &observer,
            enabled(1),
        );
        assert_eq!(observer.0.receive_tails(), 1);
        assert_eq!(observer.0.errors(), 0);
        assert_eq!(&*observer.1.drains.lock().unwrap(), &[false]);
        assert_eq!(&*observer.1.selective.lock().unwrap(), &[false]);
        assert_eq!(observer.1.proofs.lock().unwrap()[0].0, 4);
    }
}

#[test]
fn changing_selective_predicate_does_not_hide_a_late_failure() {
    fn program() -> System {
        let mut system = System::new();
        system.add(|ctx| async move {
            ctx.send(1, "a", Model::Asyn);
            ctx.send(1, "b", Model::Asyn);
            ctx.send(1, "rejected", Model::Asyn);
        });
        system.add(|ctx| async move {
            ctx.recv(|value| value == "a").await;
            ctx.recv(|value| value == "b").await;
            ctx.assert_that(false, "predicate changes must be replayed");
        });
        system
    }
    let plain = EventCountingObserver::new();
    explore(program, &plain, Config::default());
    let optimized = (EventCountingObserver::new(), TailObserver::default());
    explore(program, &optimized, enabled(1));
    assert_eq!(plain.errors(), 1);
    assert_eq!(optimized.0.errors(), plain.errors());
    assert_eq!(optimized.0.receive_tails(), 0);
}

#[test]
fn future_selective_predicate_is_reported_even_when_every_mailbox_drains() {
    let observer = (EventCountingObserver::new(), TailObserver::default());
    explore(
        || {
            let mut system = System::new();
            system.add(|ctx| async move {
                ctx.send(1, "a", Model::Asyn);
                ctx.send(1, "b", Model::Asyn);
            });
            system.add(|ctx| async move {
                ctx.recv_any().await;
                ctx.recv(|value| value == "a" || value == "b").await;
            });
            system
        },
        &observer,
        enabled(1),
    );
    assert_eq!(&*observer.1.drains.lock().unwrap(), &[true]);
    assert_eq!(&*observer.1.selective.lock().unwrap(), &[true]);
}
