//! THROWAWAY measurement harness (added for an empirical-validation task; delete after).
//!
//! Differential check of the *pruning* configuration against the *reference* traversal
//! under the current mailbox semantics, over randomly generated small programs.
//!
//!   R0  = untimed MUST (`Config::default().collect_errors()`) + post-hoc `check_mailbox`
//!   R1  = `.with_mailbox_time().with_time_filter()`                (the stated reference)
//!   R1c = R1 + `.with_certified_time()`                            (the pruning variant)
//!   Z   = `.with_mailbox_time().with_time_zombie()`                (DES reference)
//!   Zc  = Z + `.with_certified_time()`                             (DES pruning)
//!
//! Every variant is run under both `SourceOrder`s and (optionally) 1 and 2 workers, and the
//! exact `(kind, canonical_key)` sets are compared against R0. Barren/visit counters are
//! accumulated for the sequential runs so the harness also reports a barren-cut rate.
//!
//! Env knobs: `DIFF_SEED`, `DIFF_PROGS`, `DIFF_THREADS_MAX` (1 or 2), `DIFF_QUIET`.

mod common;

use std::collections::BTreeSet;

use common::SeqProgram;
use must::{
    check_mailbox, explore, Config, DeadBranchDetector, Execution, ExecutionCollector,
    ExecutionKind, Label, Model, Observer, Pred, SourceOrder, Window,
};

type Keys = BTreeSet<(u8, String)>;

#[derive(Default)]
struct Dup(std::sync::Mutex<Vec<(u8, String)>>);
impl Observer for Dup {
    fn on_execution(&self, e: &Execution, kind: ExecutionKind) {
        let k = match kind {
            ExecutionKind::Full => 0u8,
            ExecutionKind::Blocked => 1,
            ExecutionKind::Error => 2,
        };
        self.0.lock().unwrap().push((k, e.canonical_key()));
    }
}

struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

fn window(rng: &mut Rng) -> Window {
    match rng.below(4) {
        0 => Window::new(0, rng.below(2) as u64),
        1 => {
            let lo = 3 + rng.below(3) as u64;
            Window::new(lo, lo + rng.below(2) as u64)
        }
        2 => {
            let lo = rng.below(3) as u64;
            Window::new(lo, lo + 1 + rng.below(2) as u64)
        }
        _ => Window::new(0, 6),
    }
}

fn pred(rng: &mut Rng) -> Pred {
    match rng.below(4) {
        0 | 1 => Pred::any(),
        2 => Pred::eq("a"),
        _ => Pred::eq("b"),
    }
}

fn a_receive(rng: &mut Rng) -> Label {
    let p = pred(rng);
    match rng.below(3) {
        0 => Label::recv(p),
        1 => Label::recv_timeout_timed(p, window(rng)),
        _ => Label::recv_poll_timed(p, window(rng)),
    }
}

fn gen_program(rng: &mut Rng, size: usize) -> SeqProgram {
    // `size` = 0 small, 1 medium, 2 large. Thread 0 is always a receiver so the corpus is
    // dominated by programs with real rf-branching rather than degenerate straight lines.
    let n = match size {
        0 => 2 + rng.below(2),
        1 => 3 + rng.below(2),
        _ => 3 + rng.below(3),
    };
    let per = match size {
        0 => 2,
        1 => 3,
        _ => 4,
    };
    let models = [Model::Asyn, Model::P2p, Model::Mbox];
    let mut threads = Vec::new();
    for tid in 0..n {
        let len = 1 + rng.below(per);
        let mut evs = Vec::new();
        for index in 0..len {
            let lbl = if tid == 0 && index == 0 {
                a_receive(rng)
            } else if tid != 0 && index == 0 {
                // guarantee competing sends into thread 0's mailbox
                Label::send_within(
                    models[rng.below(3)],
                    0,
                    ["a", "b"][rng.below(2)],
                    window(rng),
                )
            } else {
                match rng.below(12) {
                    0..=4 => Label::send_within(
                        models[rng.below(3)],
                        rng.below(n),
                        ["a", "b"][rng.below(2)],
                        window(rng),
                    ),
                    5..=9 => a_receive(rng),
                    10 => Label::nondet(["x", "y"]),
                    _ => Label::error("boom"),
                }
            };
            evs.push(lbl);
        }
        threads.push(evs);
    }
    SeqProgram::new(threads)
}

fn keys_of(c: &ExecutionCollector, post_filter: bool) -> Keys {
    let mut out = Keys::new();
    for (k, list) in [c.full(), c.blocked(), c.errors()].into_iter().enumerate() {
        for e in list {
            if post_filter && !check_mailbox(e.graph()).is_feasible() {
                continue;
            }
            out.insert((k as u8, e.canonical_key()));
        }
    }
    out
}

struct Run {
    keys: Keys,
    dups: usize,
    visits: usize,
    barren: usize,
}

fn run(program: &SeqProgram, cfg: Config, post_filter: bool) -> Run {
    let obs = (
        (ExecutionCollector::new(), DeadBranchDetector::new()),
        Dup::default(),
    );
    explore(|| program.clone(), &obs, cfg);
    let ((collector, dead), dup) = obs;
    let recorded = dup.0.into_inner().unwrap();
    let mut seen = Keys::new();
    let mut dups = 0;
    for k in recorded {
        if !seen.insert(k) {
            dups += 1;
        }
    }
    Run {
        keys: keys_of(&collector, post_filter),
        dups,
        visits: dead.visits(),
        barren: dead.dead(),
    }
}

#[derive(Default, Clone, Copy)]
struct Tally {
    ref_visits: usize,
    ref_barren: usize,
    prune_visits: usize,
    prune_barren: usize,
}

#[test]
fn pruning_equals_reference_on_random_mailbox_programs() {
    let seed: u64 = std::env::var("DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0xD1FF_5EED_2026);
    let progs: usize = std::env::var("DIFF_PROGS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(120);
    let tmax: usize = std::env::var("DIFF_THREADS_MAX")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    let quiet = std::env::var("DIFF_QUIET").is_ok();

    let mut rng = Rng(seed);
    let mut tally = Tally::default();
    let mut divergences = 0usize;
    let mut total_terminals = 0usize;
    let mut with_blocked = 0usize;
    let mut with_error = 0usize;
    let mut with_filtered = 0usize;

    let size: usize = std::env::var("DIFF_SIZE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    for case in 0..progs {
        let program = gen_program(&mut rng, size);
        // R0: untimed MUST + post-hoc mailbox verification. Fully independent of every
        // timed traversal flag.
        let base0 = run(&program, Config::default().collect_errors(), true);
        let reference = base0.keys.clone();
        total_terminals += reference.len();
        with_blocked += reference.iter().any(|(k, _)| *k == 1) as usize;
        with_error += reference.iter().any(|(k, _)| *k == 2) as usize;

        for order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
            for des in [false, true] {
                let base = Config::default()
                    .collect_errors()
                    .with_mailbox_time()
                    .with_source_order(order);
                let base = if des {
                    base.with_time_zombie()
                } else {
                    base.with_time_filter()
                };
                for certified in [false, true] {
                    let cfg = if certified {
                        base.clone().with_certified_time()
                    } else {
                        base.clone()
                    };
                    for threads in 1..=tmax {
                        let r = run(&program, cfg.clone().with_threads(threads), false);
                        if threads == 1 && order == SourceOrder::EventId && !des {
                            if certified {
                                tally.prune_visits += r.visits;
                                tally.prune_barren += r.barren;
                            } else {
                                tally.ref_visits += r.visits;
                                tally.ref_barren += r.barren;
                                with_filtered += (r.visits > r.keys.len()) as usize;
                            }
                        }
                        let missing: Vec<_> = reference.difference(&r.keys).cloned().collect();
                        let extra: Vec<_> = r.keys.difference(&reference).cloned().collect();
                        if !missing.is_empty() || !extra.is_empty() || r.dups > 0 {
                            divergences += 1;
                            eprintln!(
                                "DIVERGENCE case={case} order={order:?} des={des} certified={certified} \
                                 threads={threads} missing={} extra={} dups={}\nprogram={:?}",
                                missing.len(),
                                extra.len(),
                                r.dups,
                                program.threads
                            );
                            for m in missing.iter().take(3) {
                                eprintln!("  MISSING {m:?}");
                            }
                            for m in extra.iter().take(3) {
                                eprintln!("  EXTRA   {m:?}");
                            }
                        }
                    }
                }
            }
        }
    }
    if !quiet {
        println!(
            "DIFFSUMMARY seed={seed:#x} progs={progs} threads_max={tmax} divergences={divergences} \
             terminals={total_terminals} progs_with_blocked={with_blocked} progs_with_error={with_error} \
             progs_where_ref_visits_exceed_terminals={with_filtered}"
        );
        println!(
            "BARREN reference visits={} barren={} | pruning visits={} barren={} | \
             barren_cut_rate={:.6}% residual_barren_fraction={:.6}%",
            tally.ref_visits,
            tally.ref_barren,
            tally.prune_visits,
            tally.prune_barren,
            100.0 * (1.0 - tally.prune_barren as f64 / tally.ref_barren.max(1) as f64),
            100.0 * tally.prune_barren as f64 / tally.prune_visits.max(1) as f64,
        );
    }
    assert_eq!(divergences, 0, "pruning diverged from the reference");
}
