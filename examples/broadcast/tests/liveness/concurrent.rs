//! Processes 0 and 1 broadcast independently, before receiving any messages.

use super::{
    common::{self, flush, NODES},
    network,
};
use crate::proc::{Factory, Outputs, Process};

pub fn run(factory: Factory) -> Result<usize, String> {
    common::run(|faulty| system(factory.clone(), faulty))
        .map_err(|error| format!("Liveness / concurrent: {error}"))
}

fn system(factory: Factory, faulty: Option<usize>) -> must::System {
    let mut sys = must::System::new();
    for id in 0..NODES {
        let factory = factory.clone();
        sys.add(move |ctx| runner(ctx, factory(id, NODES), Some(id) == faulty));
    }
    sys
}

async fn runner(ctx: must::Ctx, mut process: Box<dyn Process>, faulty: bool) {
    let mut outputs = Outputs::default();
    let mut delivered = [false; 2];

    if ctx.tid() == 0 {
        ctx.insert_label("broadcast:first");
        process.on_local_message("first", &mut outputs);
    } else if ctx.tid() == 1 {
        ctx.insert_label("broadcast:second");
        process.on_local_message("second", &mut outputs);
    }
    if !flush(&ctx, &mut outputs, &mut delivered, faulty).await {
        return;
    }

    loop {
        let Some(message) = network::recv(&ctx, faulty).await else {
            return;
        };
        process.on_message(&message, &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, faulty).await {
            return;
        }
    }
}
