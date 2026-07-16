//! Dump a `must-viz` trace of a small worker/coordinator run.
//!
//! `cargo run --example nworkers -- [-n N] [-o out.trace.json] [--threads W]`
//! Defaults: `-n 2 -o nworkers.trace.json --threads 1`. The trace loads directly in
//! `must-viz/web`. Keep `--threads 1` for one clean depth-first log.
//!
//! The program extends the `nworkers` model: `n` workers each report to a coordinator,
//! which gathers them all, replies to `main`, then broadcasts "done" back to the workers.
//! `main` first messages itself, so its receive may read its own note or the coordinator's
//! reply — the two-source choice that drives an rf-choice and a backward revisit.

use clap::Parser;
use must::event::Model;
use must::viz::TraceObserver;
use must::{explore, Config, Ctx, Program, System};

fn cluster(n: usize) -> System {
    let coord = n + 1;
    let mut sys = System::new();

    sys.add(|c: Ctx| async move {
        c.send(0, "ping", Model::P2p);
        let _ = c.recv(|_| true).await;
    });

    for w in 0..n {
        sys.add(move |c: Ctx| async move {
            c.send(coord, format!("w{w}"), Model::P2p);
            let _ = c.recv(|x: &str| x == "done").await;
        });
    }

    sys.add(move |c: Ctx| async move {
        for _ in 0..n {
            let _ = c.recv(|_| true).await;
        }
        c.send(0, "done", Model::P2p);
        for w in 1..=n {
            c.send(w, "done", Model::P2p);
        }
    });

    sys
}

#[derive(Parser)]
struct Args {
    /// Number of workers.
    #[arg(short = 'n', default_value_t = 2)]
    n: usize,
    /// Trace output path.
    #[arg(short = 'o', long = "out", default_value = "nworkers.trace.json")]
    out: String,
    /// Worker threads for the explorer (1 = one clean depth-first log).
    #[arg(long, default_value_t = 1)]
    threads: usize,
}

fn main() {
    let Args { n, out, threads } = Args::parse();

    let obs =
        TraceObserver::with_shards(format!("nworkers({n})"), cluster(n).num_threads(), threads);
    explore(
        move || cluster(n),
        &obs,
        Config::default().with_threads(threads),
    );
    obs.dump_to_file(&out).unwrap();

    let s = obs.summary();
    println!(
        "wrote {out}: {} executions ({} full, {} blocked)",
        s.full + s.blocked,
        s.full,
        s.blocked,
    );
}
