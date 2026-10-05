//! Process 0 broadcasts twice without receiving network messages in between.
//! Everyone must deliver first before second.

use super::common::{self, flush, NODES};
use crate::proc::{Factory, Outputs, Process};

pub fn run(factory: Factory) -> Result<usize, String> {
    common::run(|| system(factory.clone())).map_err(|error| format!("Safety / sequential: {error}"))
}

fn system(factory: Factory) -> must::System {
    let mut sys = must::System::new();
    for id in 0..NODES {
        let factory = factory.clone();
        sys.add(move |ctx| runner(ctx, factory(id, NODES)));
    }
    sys
}

async fn runner(ctx: must::Ctx, mut process: Box<dyn Process>) {
    let mut outputs = Outputs::default();
    let mut delivered = [false; 2];

    if ctx.tid() == 0 {
        ctx.insert_label("broadcast:first");
        process.on_local_message("first", &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }

        // No network receive or wait for delivery between the two broadcasts.
        ctx.insert_label("broadcast:second");
        process.on_local_message("second", &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }

    loop {
        let message = ctx.recv_any().await;
        process.on_message(&message, &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }
}
