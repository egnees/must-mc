//! Native fixtures exercise both accepted executions and actual counterexamples.

use std::sync::{Arc, OnceLock};

use crate::proc::{Factory, Output, Outputs};
use crate::solutions;

use super::common::{BROADCAST, DELIVERED, MESSAGES, NODES};

#[derive(Default)]
struct Outcome {
    failure: OnceLock<String>,
    required_delivery: Option<must::Val>,
}

impl must::Observer for Outcome {
    fn should_stop(&self) -> bool {
        self.failure.get().is_some()
    }

    fn on_execution(&self, execution: &must::Execution, kind: must::ExecutionKind) {
        if kind == must::ExecutionKind::Error {
            self.failure
                .get_or_init(|| must::render::render_execution(execution));
            return;
        }
        if let Some(delivery) = self.required_delivery {
            let mut counts = [0; NODES];
            for label in execution.labels() {
                if label.value == delivery {
                    counts[label.tid] += 1;
                }
            }
            if let Some(tid) = counts.iter().position(|&count| count != 1) {
                self.failure
                    .get_or_init(|| format!("Node {tid} did not deliver exactly once"));
            }
        }
    }
}

fn single_message_without_faults(factory: Factory) {
    let observer = (
        must::CountingObserver::new(),
        Outcome {
            required_delivery: Some(must::intern::intern(DELIVERED[0])),
            ..Outcome::default()
        },
    );
    must::explore(
        || {
            let mut system = must::System::new();
            for tid in 0..NODES {
                let factory = factory.clone();
                system.add(move |ctx| {
                    let mut process = factory(tid, NODES);
                    async move {
                        let mut outputs = Outputs::default();
                        let mut delivered = [false; 2];
                        if tid == 0 {
                            ctx.insert_label(BROADCAST[0]);
                            process.on_local_message(MESSAGES[0], &mut outputs);
                            if !super::common::flush(&ctx, &mut outputs, &mut delivered, false) {
                                return;
                            }
                        }
                        loop {
                            process.on_message(&ctx.recv_any().await, &mut outputs);
                            if !super::common::flush(&ctx, &mut outputs, &mut delivered, false) {
                                return;
                            }
                        }
                    }
                });
            }
            system
        },
        &observer,
        must::Config::default()
            .with_threads(12)
            .with_stop_on_terminal_error(),
    );
    assert!(observer.0.full() + observer.0.blocked() > 0);
    let failure = observer.1.failure.get();
    assert!(failure.is_none(), "{failure:?}");
}

fn fails(factory: Factory, scenario: super::Scenario, reasons: &[&str]) {
    let error = scenario(factory).expect_err("faulty solution must produce a counterexample");
    assert!(!error.contains("incomplete"), "{error}");
    assert!(
        reasons.iter().any(|reason| error.contains(reason)),
        "{error}"
    );
}

#[test]
fn causal_passes_all_five_scenarios() {
    for (_, scenario) in super::SCENARIOS {
        scenario(Arc::new(solutions::causal::new)).unwrap();
    }
}

macro_rules! faulty_solution {
    ($name:ident, $scenario:ident, $($reason:literal),+) => {
        #[test]
        fn $name() {
            let factory: Factory = Arc::new(solutions::$name::new);
            single_message_without_faults(factory.clone());
            fails(factory, super::$scenario::run, &[$($reason),+]);
        }
    };
}

faulty_solution!(direct, concurrent, "uniform agreement");
faulty_solution!(send_then_deliver, concurrent, "uniform agreement");
faulty_solution!(majority_ack, sequential, "validity", "uniform agreement");
faulty_solution!(flood, concurrent, "uniform agreement");
faulty_solution!(outbox_sequence, after_delivery, "validity");
faulty_solution!(prefix_clock, reverse_reply, "Causal Order");

fn reply_to_two_independent_broadcasts(factory: Factory) -> Option<String> {
    let observer = Outcome::default();
    must::explore(
        || {
            let mut system = must::System::new();
            for tid in 0..NODES {
                let factory = factory.clone();
                system.add(move |ctx| {
                    let mut process = factory(tid, NODES);
                    async move {
                        let mut outputs = Outputs::default();
                        let mut delivered = [false; 3];
                        let mut replied = false;
                        if tid < 2 {
                            process.on_local_message(MESSAGES[tid], &mut outputs);
                        }
                        loop {
                            for output in outputs.take() {
                                match output {
                                    Output::Message { to, message } => {
                                        ctx.send(to, message, must::Model::Asyn)
                                    }
                                    Output::Error(error) => {
                                        ctx.assert_that(false, &error);
                                        return;
                                    }
                                    Output::LocalMessage(message) => {
                                        let index = ["first", "second", "reply"]
                                            .iter()
                                            .position(|&text| text == message)
                                            .unwrap();
                                        ctx.assert_that(!delivered[index], "duplicate delivery");
                                        ctx.assert_that(
                                            index != 2 || delivered[0] && delivered[1],
                                            "Causal Order violated: reply overtook a predecessor",
                                        );
                                        delivered[index] = true;
                                    }
                                }
                            }
                            if tid == 2 && delivered[0] && delivered[1] && !replied {
                                replied = true;
                                process.on_local_message("reply", &mut outputs);
                            } else {
                                process.on_message(&ctx.recv_any().await, &mut outputs);
                            }
                        }
                    }
                });
            }
            system
        },
        &observer,
        must::Config::default()
            .with_threads(12)
            .with_stop_on_terminal_error(),
    );
    observer.failure.into_inner()
}

#[test]
fn last_dependency() {
    let factory: Factory = Arc::new(solutions::last_dependency::new);
    single_message_without_faults(factory.clone());
    let error = reply_to_two_independent_broadcasts(factory)
        .expect("forgotten concurrent predecessor must fail");
    assert!(error.contains("Causal Order"), "{error}");
}

#[test]
fn early_gc() {
    let factory: Factory = Arc::new(solutions::early_gc::new);
    single_message_without_faults(factory.clone());
    let error = reply_to_two_independent_broadcasts(factory)
        .expect("prematurely discarded predecessor must fail");
    assert!(error.contains("Causal Order"), "{error}");
}
