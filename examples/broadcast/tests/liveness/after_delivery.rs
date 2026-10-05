//! Process 0 broadcasts second only after locally delivering its own first broadcast.
//! It may crash between that delivery and the second application input.

use super::{
    common::{self, flush, NODES},
    network,
};
use crate::{
    proc::{Factory, Outputs, Process},
    tests::common::crash,
};

pub fn run(factory: Factory) -> Result<usize, String> {
    common::run(|faulty| system(factory.clone(), faulty))
        .map_err(|error| format!("Liveness / after_delivery: {error}"))
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
    let mut sent_second = false;

    if ctx.tid() == 0 {
        ctx.insert_label("broadcast:first");
        process.on_local_message("first", &mut outputs);
        if !flush(&ctx, &mut outputs, &mut delivered, faulty).await {
            return;
        }
    }

    loop {
        if ctx.tid() == 0 && delivered[0] && !sent_second {
            if faulty && crash(&ctx).await {
                ctx.insert_label("crash");
                return;
            }
            sent_second = true;
            ctx.insert_label("broadcast:second");
            process.on_local_message("second", &mut outputs);
        } else {
            let Some(message) = network::recv(&ctx, faulty).await else {
                return;
            };
            process.on_message(&message, &mut outputs);
        }
        if !flush(&ctx, &mut outputs, &mut delivered, faulty).await {
            return;
        }
    }
}
