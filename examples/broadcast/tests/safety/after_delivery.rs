//! Process 0 broadcasts second only after locally delivering its own first broadcast.
//! Everyone must deliver first before second.

use super::common::{self, flush, NODES};
use crate::proc::{Factory, Outputs, Process};

pub fn run(factory: Factory) -> Result<usize, String> {
    common::run(|| system(factory.clone()))
        .map_err(|error| format!("Safety / after_delivery: {error}"))
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
    let mut sent_second = false;

    if ctx.tid() == 0 {
        ctx.insert_label("broadcast:first");
        process.on_local_message("first", &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }

    loop {
        if ctx.tid() == 0 && delivered[0] && !sent_second {
            sent_second = true;
            ctx.insert_label("broadcast:second");
            process.on_local_message("second", &mut outputs);
        } else {
            let message = ctx.recv_any().await;
            process.on_message(&message, &mut outputs);
        }
        if !flush(&ctx, &mut outputs, &mut delivered, true) {
            return;
        }
    }
}
