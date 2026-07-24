//! Cross-model execution-count and wall-clock comparison for the 2PC and leader-election
//! models: models as columns, execution count and time per cell, at small instances.
//!
//! Two qualitative findings are checked:
//!   * Monitors are nearly free. The selective-notification monitors here add exactly 0%
//!     extra executions, well under the 20% cap the test enforces. Asserted.
//!   * mbox is the slowest check (global acyclicity versus the cheaper ordering checks of
//!     p2p and cd). Printed for inspection, since wall-clock time is environment dependent.
//!
//! The execution count is model-independent here because every receive is selective by
//! sender, so `rf` is deterministic. That equality guards against an over-restrictive
//! consistency check that wrongly prunes graphs; the ordering clauses themselves are
//! covered by `tests/models.rs`.
//!
//! These are benchmarks (they print a table and run larger instances), so they run only in
//! release builds. To see the table: `cargo test --release --test comparison -- --nocapture`.

mod common;

use std::time::Instant;

use common::{leader_system, twopc_system, LeaderBug, TwoPcBug};
use must::event::Model;
use must::{explore, Config, CountingObserver, System};

const MODELS: [(Model, &str); 4] = [
    (Model::Asyn, "asyn"),
    (Model::P2p, "p2p"),
    (Model::Cd, "cd"),
    (Model::Mbox, "mbox"),
];

/// Terminal execution count and wall-clock time of one `explore` run (default priorities).
fn count_and_time(make: impl Fn() -> System + Sync) -> (usize, f64) {
    let obs = CountingObserver::new();
    let start = Instant::now();
    explore(make, &obs, Config::default());
    let ms = start.elapsed().as_secs_f64() * 1000.0;
    (obs.terminal(), ms)
}

/// Build the system for each model, time it, assert the count is model-independent, and
/// print one table row `label | execs | per-model time`.
fn compare_row(label: &str, build: impl Fn(Model) -> System + Sync) {
    let mut execs: Option<usize> = None;
    let mut cells: Vec<String> = Vec::new();
    for (m, name) in MODELS {
        let (c, ms) = count_and_time(|| build(m));
        match execs {
            None => execs = Some(c),
            Some(prev) => assert_eq!(
                c, prev,
                "{label}: exec count under {name} ({c}) differs from other models ({prev})"
            ),
        }
        cells.push(format!("{name}={ms:>8.2}ms"));
    }
    println!(
        "{label:<20} execs={:>7}   {}",
        execs.unwrap(),
        cells.join("  ")
    );
}

/// The headline table: execution count (model-independent) and wall-clock per model.
#[test]
#[cfg_attr(debug_assertions, ignore = "benchmark; run with --release")]
fn cross_model_table() {
    println!("\n== 2PC / leader election: execs (model-independent) & wall-clock per model ==");
    compare_row("twopc(3)", |m| {
        twopc_system(3, m, false, false, TwoPcBug::None)
    });
    compare_row("twopc_crash(4)", |m| {
        twopc_system(4, m, true, false, TwoPcBug::None)
    });
    compare_row("leader(2,3)", |m| {
        leader_system(2, 3, m, false, false, LeaderBug::None)
    });
    compare_row("leader(3,2)", |m| {
        leader_system(3, 2, m, false, false, LeaderBug::None)
    });
    compare_row("leader(2,4)", |m| {
        leader_system(2, 4, m, false, false, LeaderBug::None)
    });
    compare_row("leader_crash(3,1)", |m| {
        leader_system(3, 1, m, true, false, LeaderBug::None)
    });
    println!(
        "\nexecs equal across models (selective receives => deterministic rf); \
         mbox is typically slowest (global-acyclicity check)."
    );
}

/// Monitors are nearly free: ours add 0% extra executions, well under the 20% cap.
#[test]
#[cfg_attr(debug_assertions, ignore = "benchmark; run with --release")]
fn monitor_overhead() {
    println!("\n== Monitor overhead (leader(2,3), p2p) ==");
    let (cb, tb) =
        count_and_time(|| leader_system(2, 3, Model::P2p, false, false, LeaderBug::None));
    let (cm, tm) = count_and_time(|| leader_system(2, 3, Model::P2p, false, true, LeaderBug::None));
    let overhead = (cm as f64 / cb as f64 - 1.0) * 100.0;
    println!("base : execs={cb:>7}  {tb:>8.2}ms");
    println!("+mon : execs={cm:>7}  {tm:>8.2}ms   (exec overhead {overhead:.1}%)");
    // Factor-1 on the count (selective notifications), well inside the 20% cap.
    assert_eq!(
        cb, cm,
        "monitor must not change the execution count (factor-1)"
    );
    assert!(
        cm as f64 <= 1.2 * cb as f64,
        "monitor exec overhead exceeded the 20% bound"
    );
}
