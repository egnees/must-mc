use std::sync::OnceLock;

use crate::proc::{Factory, Output, Outputs, Process};

static THREADS: OnceLock<usize> = OnceLock::new();

pub fn configure(threads: usize) {
    THREADS
        .set(threads.max(1))
        .expect("configure broadcast once");
}

pub(crate) fn threads() -> usize {
    THREADS.get().copied().unwrap_or(12)
}

pub(super) const NODES: usize = 3;
pub(super) const MESSAGES: [&str; 2] = ["first", "second"];
pub(super) const BROADCAST: [&str; 2] = ["broadcast:first", "broadcast:second"];
pub(super) const DELIVERED: [&str; 2] = ["deliver:first", "deliver:second"];
#[derive(Default)]
struct FirstFailure {
    trace: OnceLock<String>,
}

impl FirstFailure {
    fn fail(&self, graph: &must::ExecutionGraph, labels: &[must::TraceLabel], reason: &str) {
        self.trace.get_or_init(|| {
            format!(
                "{reason}\nSource failure-free execution (not the cut):\n{}",
                must::render::render_execution_view(graph, labels)
            )
        });
    }
}

impl must::Observer for FirstFailure {
    fn should_stop(&self) -> bool {
        self.trace.get().is_some()
    }

    fn inspects_rf_trial_graphs(&self) -> bool {
        false
    }

    fn inspects_revisit_targets(&self) -> bool {
        false
    }

    fn observes_rejected_rf_trials(&self) -> bool {
        false
    }

    fn allows_buffered_events(&self) -> bool {
        true
    }

    fn receive_tail_candidate(
        &self,
        _graph: &must::ExecutionGraph,
        labels: &[must::TraceLabel],
    ) -> bool {
        if self.trace.get().is_some() {
            return false;
        }
        static SYMBOLS: OnceLock<([must::Val; 2], [must::Val; 2])> = OnceLock::new();
        let (broadcasts, deliveries) = SYMBOLS.get_or_init(|| {
            (
                BROADCAST.map(must::intern::intern),
                DELIVERED.map(must::intern::intern),
            )
        });
        let mut active = [false; 2];
        let mut delivered = [[false; NODES]; 2];
        for label in labels {
            for message in 0..2 {
                if label.value == broadcasts[message] {
                    active[message] = true;
                }
                if label.value == deliveries[message] && label.tid < NODES {
                    active[message] = true;
                    delivered[message][label.tid] = true;
                }
            }
        }
        active.iter().any(|&present| present)
            && (0..2).all(|message| !active[message] || delivered[message].iter().all(|&done| done))
    }

    fn accept_receive_tail(
        &self,
        certificate: &must::explorer::receive_tail::ReceiveTailCertificate<'_>,
    ) -> bool {
        super::cuts::prove_completed_receive_tail(
            certificate.graph(),
            certificate.labels(),
            certificate.pending_sends(),
        )
    }

    fn on_execution(&self, execution: &must::Execution, kind: must::ExecutionKind) {
        self.on_execution_view(execution.graph(), execution.labels(), kind);
    }

    fn accepts_execution_view(&self) -> bool {
        true
    }

    fn on_execution_view(
        &self,
        graph: &must::ExecutionGraph,
        labels: &[must::TraceLabel],
        kind: must::ExecutionKind,
    ) {
        if self.trace.get().is_some() {
            return;
        }
        if kind == must::ExecutionKind::Error {
            self.fail(graph, labels, "Broadcast assertion failed");
            return;
        }

        match super::cuts::analyze_graph(graph, labels) {
            Ok(Some(failure)) => self.fail(graph, labels, &failure.to_string()),
            Ok(None) => {}
            Err(error) => self.fail(
                graph,
                labels,
                &format!("Broadcast check incomplete: {error}"),
            ),
        }
    }
}

pub(super) fn run(make_system: impl Fn() -> must::System + Sync) -> Result<usize, String> {
    let observer = (
        must::EventCountingObserver::with_shards(threads()).with_buffered_events(),
        FirstFailure::default(),
    );
    must::explore(
        make_system,
        &observer,
        must::Config::default()
            .with_threads(threads())
            .with_stop_on_terminal_error()
            .with_receive_tail(must::explorer::receive_tail::ReceiveTailBudget::default()),
    );
    if let Some(error) = observer.1.trace.into_inner() {
        return Err(error);
    }
    assert!(observer.0.full() + observer.0.blocked() + observer.0.receive_tails() > 0);
    Ok(observer.0.events_added())
}

pub(super) fn reply_system(factory: Factory, sender: usize, responder: usize) -> must::System {
    let mut system = must::System::new();
    for tid in 0..NODES {
        let factory = factory.clone();
        system.add(move |ctx| reply_process(ctx, factory(tid, NODES), sender, responder));
    }
    system
}

async fn reply_process(
    ctx: must::Ctx,
    mut process: Box<dyn Process>,
    sender: usize,
    responder: usize,
) {
    let mut outputs = Outputs::default();
    let mut delivered = [false; 2];
    let mut replied = false;

    if ctx.tid() == sender {
        ctx.insert_label(BROADCAST[0]);
        process.on_local_message(MESSAGES[0], &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }

    loop {
        if ctx.tid() == responder && delivered[0] && !replied {
            ctx.insert_label("crash:boundary");
            replied = true;
            ctx.insert_label(BROADCAST[1]);
            process.on_local_message(MESSAGES[1], &mut outputs);
        } else {
            let message = receive(&ctx, process.as_ref()).await;
            process.on_message(&message, &mut outputs);
        }
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }
}

pub(super) async fn receive(ctx: &must::Ctx, process: &dyn Process) -> String {
    match process.receive_predicate() {
        Some(predicate) => ctx.recv(move |message| predicate(message)).await,
        None => ctx.recv_any().await,
    }
}

pub(super) fn flush(
    ctx: &must::Ctx,
    outputs: &mut Outputs,
    delivered: &mut [bool; 2],
    ordered: bool,
) -> bool {
    for output in outputs.take() {
        match output {
            Output::Error(message) => {
                ctx.assert_that(false, &message);
                return false;
            }
            Output::LocalMessage(message) => deliver_local(ctx, &message, delivered, ordered),
            Output::Message { to, message } => {
                ctx.assert_that(to < NODES, "broadcast destination is out of range");
                if to >= NODES {
                    return false;
                }
                ctx.send(to, message, must::Model::Asyn);
            }
        }
    }
    true
}

fn deliver_local(ctx: &must::Ctx, message: &str, delivered: &mut [bool; 2], ordered: bool) {
    let Some(index) = MESSAGES.iter().position(|&value| value == message) else {
        ctx.assert_that(false, "broadcast payload was corrupted");
        return;
    };
    ctx.assert_that(
        !delivered[index],
        "broadcast delivered locally more than once",
    );
    ctx.assert_that(
        !ordered || index == 0 || delivered[0],
        "Causal Order violated: delivered second before first",
    );
    delivered[index] = true;
    ctx.insert_label(DELIVERED[index]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_known_payload_delivered_before_its_broadcast() {
        let error = run(|| {
            let mut system = must::System::new();
            for tid in 0..NODES {
                system.add(move |ctx| async move {
                    ctx.insert_label(DELIVERED[0]);
                    if tid == 0 {
                        ctx.insert_label(BROADCAST[0]);
                    }
                });
            }
            system
        })
        .unwrap_err();
        assert!(error.contains("no creation"), "{error}");
    }

    #[test]
    fn checks_causal_order_duplication_and_unknown_payloads_at_delivery() {
        for (messages, ordered, expected_error) in [
            (&["second", "first"][..], false, None),
            (&["second", "first"][..], true, Some("Causal Order")),
            (&["first", "first"][..], false, Some("more than once")),
            (&["invented"][..], false, Some("corrupted")),
        ] {
            let observer = must::ExecutionCollector::new();
            must::explore(
                || {
                    let mut system = must::System::new();
                    system.add(move |ctx| async move {
                        let mut outputs = Outputs::default();
                        for message in messages {
                            outputs.send_local_message((*message).to_owned());
                        }
                        flush(&ctx, &mut outputs, &mut [false; 2], ordered);
                    });
                    system
                },
                &observer,
                must::Config::default(),
            );
            let errors = observer.errors();
            if let Some(reason) = expected_error {
                assert_eq!(errors.len(), 1);
                let trace = must::render::render_execution(&errors[0]);
                assert!(trace.contains(reason), "{trace}");
            } else {
                assert!(errors.is_empty());
                assert_eq!(observer.full_count(), 1);
            }
        }
    }
}
