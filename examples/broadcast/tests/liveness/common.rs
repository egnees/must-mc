use std::sync::OnceLock;

use super::network;
use crate::{
    proc::{Output, Outputs},
    tests::common::{crash, max_sends, threads},
};

pub(super) const NODES: usize = 3;
const MESSAGES: [&str; 2] = ["first", "second"];
const BROADCAST: [&str; 2] = ["broadcast:first", "broadcast:second"];
const DELIVERED: [&str; 2] = ["deliver:first", "deliver:second"];
const CRASH: &str = "crash";

#[derive(Default)]
struct FirstFailure {
    trace: OnceLock<String>,
}

impl FirstFailure {
    fn fail(&self, execution: &must::Execution, reason: &str) {
        self.trace
            .get_or_init(|| format!("{reason}\n{}", must::render::render_execution(execution)));
    }
}

impl must::Observer for FirstFailure {
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

    fn on_execution(&self, execution: &must::Execution, kind: must::ExecutionKind) {
        if self.trace.get().is_some() {
            return;
        }
        if kind == must::ExecutionKind::Error {
            self.fail(execution, "Broadcast assertion failed");
            return;
        }

        for message in 0..2 {
            let mut sender = None;
            let mut delivered = [false; NODES];
            let mut crashed = [false; NODES];
            for label in execution.labels() {
                let value = must::intern::resolve(label.value);
                if value == BROADCAST[message] {
                    sender = Some(label.tid);
                }
                if value == DELIVERED[message] {
                    delivered[label.tid] = true;
                }
                if value == CRASH {
                    crashed[label.tid] = true;
                }
            }

            // Validity: a live sender must deliver its actual broadcast.
            if let Some(sender) = sender {
                if !crashed[sender] && !delivered[sender] {
                    self.fail(
                        execution,
                        &format!(
                            "validity violated: sender {sender} did not deliver {:?}",
                            MESSAGES[message]
                        ),
                    );
                    return;
                }
            }

            // Uniform Agreement: any delivery requires delivery at every live node.
            if delivered.contains(&true) {
                for node in 0..NODES {
                    if !crashed[node] && !delivered[node] {
                        self.fail(
                            execution,
                            &format!(
                                "uniform agreement violated: node {node} did not deliver {:?}",
                                MESSAGES[message]
                            ),
                        );
                        return;
                    }
                }
            }
        }
    }

    fn on_send_limit(&self, graph: &must::ExecutionGraph, limit: usize) {
        self.trace.get_or_init(|| {
            format!(
                "Broadcast liveness check incomplete: send limit {limit} exceeded\n\
                 Execution prefix before the next send:\n{}",
                must::render::render_graph(graph)
            )
        });
    }
}

pub(super) fn run(
    make_system: impl Fn(Option<usize>) -> must::System + Sync,
) -> Result<usize, String> {
    let mut events = 0;
    for faulty in std::iter::once(None).chain((0..NODES).map(Some)) {
        let observer = (
            must::EventCountingObserver::with_shards(threads()).with_buffered_events(),
            FirstFailure::default(),
        );
        must::explore(
            || {
                let mut system = make_system(faulty);
                network::add_sink(&mut system);
                system
            },
            &observer,
            must::Config::default()
                .with_threads(threads())
                .with_max_sends(max_sends())
                .with_stop_on_terminal_error(),
        );

        if let Some(error) = observer.1.trace.into_inner() {
            let case = match faulty {
                Some(node) => format!(
                    "Node {node} crashes. Sends to T{NODES} represent packets lost at its crash."
                ),
                None => "No crashes.".to_owned(),
            };
            return Err(format!("{case}\n{error}"));
        }
        assert!(observer.0.full() + observer.0.blocked() > 0);
        events += observer.0.events_added();
    }
    Ok(events)
}

pub(super) async fn flush(
    ctx: &must::Ctx,
    outputs: &mut Outputs,
    delivered: &mut [bool; 2],
    faulty: bool,
) -> bool {
    for output in outputs.take() {
        match output {
            Output::Error(message) => {
                ctx.assert_that(false, &message);
                return false;
            }
            Output::LocalMessage(message) => deliver_local(ctx, &message, delivered),
            Output::Message { to, message } => {
                ctx.assert_that(to < NODES, "broadcast destination is out of range");
                if to >= NODES {
                    return false;
                }
                if faulty && crash(ctx).await {
                    ctx.insert_label(CRASH);
                    return false;
                }
                network::send(ctx, to, message, faulty).await;
            }
        }
    }
    true
}

fn deliver_local(ctx: &must::Ctx, message: &str, delivered: &mut [bool; 2]) {
    let Some(index) = MESSAGES.iter().position(|&value| value == message) else {
        ctx.assert_that(false, "broadcast payload was corrupted");
        return;
    };
    ctx.assert_that(
        !delivered[index],
        "broadcast delivered locally more than once",
    );
    delivered[index] = true;
    ctx.insert_label(DELIVERED[index]);
}
