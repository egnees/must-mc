//! Process 0 broadcasts twice without receiving network messages in between.
//! It may crash between these two application inputs.

use super::common::{self, flush, BROADCAST, MESSAGES, NODES};
use crate::proc::{Factory, Outputs, Process};

pub fn run(factory: Factory) -> Result<usize, String> {
    common::run(|| system(factory.clone())).map_err(|error| format!("sequential: {error}"))
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

    if ctx.tid() == 0 {
        ctx.insert_label(BROADCAST[0]);
        process.on_local_message(MESSAGES[0], &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }

        ctx.insert_label("crash:boundary");
        ctx.insert_label(BROADCAST[1]);
        process.on_local_message(MESSAGES[1], &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }

    loop {
        let message = common::receive(&ctx, process.as_ref()).await;
        process.on_message(&message, &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }
}
