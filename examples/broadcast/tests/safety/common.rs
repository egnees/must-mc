use std::sync::OnceLock;

use crate::{
    proc::{Output, Outputs},
    tests::common::{max_sends, threads},
};

pub(super) const NODES: usize = 3;
const MESSAGES: [&str; 2] = ["first", "second"];
const BROADCAST: [&str; 2] = ["broadcast:first", "broadcast:second"];
const DELIVERED: [&str; 2] = ["deliver:first", "deliver:second"];

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
            self.fail(execution, "Safety violation");
            return;
        }

        // A known payload can still be invented before its application input.
        // Each delivery must follow that input, not merely share its final trace.
        let labels = execution.labels();
        for (delivery, label) in labels.iter().enumerate() {
            let Some(message) = DELIVERED
                .iter()
                .position(|&value| value == must::intern::resolve(label.value))
            else {
                continue;
            };
            let broadcast = labels
                .iter()
                .position(|label| must::intern::resolve(label.value) == BROADCAST[message]);
            if !broadcast.is_some_and(|broadcast| precedes(execution, broadcast, delivery)) {
                self.fail(
                    execution,
                    &format!(
                        "No Creation violated at node {}: {:?} before its broadcast",
                        label.tid, MESSAGES[message]
                    ),
                );
                return;
            }
        }
    }

    fn on_send_limit(&self, graph: &must::ExecutionGraph, limit: usize) {
        self.trace.get_or_init(|| {
            // A resource cutoff cannot prove or refute the three safety properties.
            format!(
                "Safety check incomplete: send limit {limit} exceeded\n{}",
                must::render::render_graph(graph)
            )
        });
    }
}

// Check order in every interleaving represented by this untimed graph.
// Without a po/rf path, a delivery can occur before its application input.
fn precedes(execution: &must::Execution, before: usize, after: usize) -> bool {
    let source = &execution.labels()[before];
    let target = &execution.labels()[after];
    if source.tid == target.tid {
        return before < after; // Includes labels between the same two events.
    }
    let Some(previous) = target.position.checked_sub(1) else {
        return false;
    };
    // Labels sit between events: source -> next event -> ... -> previous event -> target.
    let next = must::EventId::new(source.tid, source.position);
    let previous = must::EventId::new(target.tid, previous);
    let graph = execution.graph();
    graph.contains(next) && graph.porf_reaches(next, previous)
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
            .with_max_sends(max_sends()),
    );
    if let Some(error) = observer.1.trace.into_inner() {
        return Err(error);
    }
    if observer.0.full() + observer.0.blocked() == 0 {
        return Err("Safety check produced no completed executions".into());
    }
    Ok(observer.0.events_added())
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
        ctx.assert_that(
            false,
            &format!("No Creation violated: unknown message {message:?}"),
        );
        return;
    };
    ctx.assert_that(
        !delivered[index],
        &format!("No Duplication violated: {message:?}"),
    );
    if ordered && index == 1 {
        ctx.assert_that(
            delivered[0],
            "Causal Order violated: second delivered before first",
        );
    }
    delivered[index] = true;
    ctx.insert_label(DELIVERED[index]);
}
