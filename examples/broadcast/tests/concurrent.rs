//! Processes 0 and 1 broadcast independently, before receiving any messages.

use super::common::{self, flush, BROADCAST, MESSAGES, NODES};
use crate::proc::{Factory, Outputs, Process};

pub fn run(factory: Factory) -> Result<usize, String> {
    common::run(|| system(factory.clone())).map_err(|error| format!("concurrent: {error}"))
}

pub(super) fn system(factory: Factory) -> must::System {
    let mut system = must::System::new();
    for id in 0..NODES {
        let factory = factory.clone();
        system.add(move |ctx| runner(ctx, factory(id, NODES)));
    }
    system
}

async fn runner(ctx: must::Ctx, mut process: Box<dyn Process>) {
    let mut outputs = Outputs::default();
    let mut delivered = [false; 2];

    if ctx.tid() < MESSAGES.len() {
        ctx.insert_label(BROADCAST[ctx.tid()]);
        process.on_local_message(MESSAGES[ctx.tid()], &mut outputs);
    }
    if !flush(&ctx, &mut outputs, &mut delivered, false) {
        return;
    }

    loop {
        let message = common::receive(&ctx, process.as_ref()).await;
        process.on_message(&message, &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, false) {
            return;
        }
    }
}
