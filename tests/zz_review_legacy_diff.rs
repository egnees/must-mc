//! REVIEW ARTIFACT (added by an independent completeness review; safe to delete).
//!
//! `tests/zz_validation_diff.rs` fuzzes only the **mailbox** timing regime, in which
//! `Explorer::certified_prune` returns before ever reaching the legacy
//! semantic/coverage fallback (`time::future::check_completion` +
//! `explorer::ownership::certify_no_escape`) and in which `permanent_blocker` is
//! restricted to its ancestral-Asyn arm. Those code paths — the non-ancestral /
//! P2p blocker trial, the bounded lookahead and the no-escape walk — are therefore
//! covered only by hand-written fixtures.
//!
//! This harness closes that gap: random small **legacy-timed** programs (Asyn/P2p
//! sends with windows, blocking and abstract non-blocking receives, nondets, errors)
//! are explored with
//!
//!   REF  = `Config::default().collect_errors().with_time_filter()`
//!   C1   = REF + `.with_certified_time()`
//!   C2   = `.with_certified_time()` alone (which turns on the DES/zombie policy)
//!
//! under both `SourceOrder`s, several priority permutations and 1..=2 workers, and the
//! exact `(kind, canonical_key)` sets are compared. A missing key is a completeness
//! (A) violation; an extra key or a repeat is an optimality violation.
//!
//! `SeqProgram` supplies an *exact* `possible_future`, so the no-send exemption in
//! `frozen::refute_first_alteration_sources` and the source-exclusion reasoning in
//! `time::future` are both live here.
//!
//! Knobs: `LEG_SEED`, `LEG_PROGS`, `LEG_THREADS_MAX`.

mod common;

use std::collections::BTreeSet;

use common::SeqProgram;
use must::{
    explore, Config, Execution, ExecutionKind, Label, Model, Observer, Pred, SourceOrder, Window,
};

type Keys = BTreeSet<(u8, String)>;

#[derive(Default)]
struct Rec(std::sync::Mutex<Vec<(u8, String)>>);

impl Observer for Rec {
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
    match rng.below(5) {
        0 => Window::new(0, 0),
        1 => Window::new(1, 1),
        2 => {
            let lo = rng.below(4) as u64;
            Window::new(lo, lo + rng.below(3) as u64)
        }
        3 => Window::new(5, 9),
        _ => Window::new(0, 4),
    }
}

fn pred(rng: &mut Rng) -> Pred {
    match rng.below(4) {
        0 | 1 => Pred::any(),
        2 => Pred::eq("a"),
        _ => Pred::eq("b"),
    }
}

/// Legacy timing supports Asyn and P2p only (`time::assert_supported_models`).
fn a_send(rng: &mut Rng, dst: usize) -> Label {
    let model = if rng.below(2) == 0 {
        Model::Asyn
    } else {
        Model::P2p
    };
    Label::send_within(model, dst, ["a", "b"][rng.below(2)], window(rng))
}

fn a_recv(rng: &mut Rng) -> Label {
    let p = pred(rng);
    if rng.below(4) == 0 {
        Label::recv_nb(p)
    } else {
        Label::recv(p)
    }
}

fn gen_program(rng: &mut Rng) -> SeqProgram {
    let n = 3 + rng.below(2);
    let mut threads: Vec<Vec<Label>> = Vec::new();
    for tid in 0..n {
        let len = 1 + rng.below(3);
        let mut evs = Vec::new();
        for index in 0..len {
            let lbl = if tid == 0 && index == 0 {
                a_recv(rng)
            } else if tid != 0 && index == 0 {
                // Guarantee competing sends into thread 0's mailbox, so the blocking
                // anchor rule and the first-alteration rule both have material.
                a_send(rng, 0)
            } else {
                match rng.below(12) {
                    0..=5 => {
                        let dst = rng.below(n);
                        a_send(rng, dst)
                    }
                    6..=9 => a_recv(rng),
                    10 => Label::nondet(["x", "y"]),
                    _ => Label::error("boom"),
                }
            };
            evs.push(lbl);
        }
        threads.push(evs);
    }
    // Some programs get a thread that provably never sends again: this is the shape
    // `refute_first_alteration_sources` discharges through `possible_future`.
    if rng.below(3) == 0 {
        threads[n - 1] = vec![a_recv(rng), a_recv(rng)];
    }
    SeqProgram::new(threads)
}

fn run(program: &SeqProgram, cfg: Config) -> (Keys, usize) {
    let obs = Rec::default();
    explore(|| program.clone(), &obs, cfg);
    let recorded = obs.0.into_inner().unwrap();
    let mut keys = Keys::new();
    let mut dups = 0;
    for k in recorded {
        if !keys.insert(k) {
            dups += 1;
        }
    }
    (keys, dups)
}

#[test]
fn legacy_certified_pruning_equals_terminal_filter_reference() {
    let seed: u64 = std::env::var("LEG_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x1E9A_C0DE_2026);
    let progs: usize = std::env::var("LEG_PROGS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(150);
    let tmax: usize = std::env::var("LEG_THREADS_MAX")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);

    let mut rng = Rng(seed);
    let mut divergences = 0usize;
    let mut terminals = 0usize;

    for case in 0..progs {
        let program = gen_program(&mut rng);
        let n = program.threads.len();

        let mut orders: Vec<Vec<usize>> = vec![(0..n).collect(), (0..n).rev().collect()];
        let mut rotated: Vec<usize> = (0..n).collect();
        rotated.rotate_left(1);
        orders.push(rotated);

        for priorities in orders {
            let base = Config::default()
                .collect_errors()
                .with_priorities(priorities.clone());
            let (reference, ref_dups) = run(&program, base.clone().with_time_filter());
            assert_eq!(ref_dups, 0, "reference produced a duplicate (case {case})");
            terminals += reference.len();

            for order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
                let ordered = base.clone().with_source_order(order);
                for cfg in [
                    ordered.clone().with_time_filter().with_certified_time(),
                    ordered.clone().with_certified_time(),
                    // A zero budget must disable every certificate and preserve the set.
                    ordered
                        .clone()
                        .with_time_filter()
                        .with_certified_time_budget(0, 0),
                ] {
                    for threads in 1..=tmax {
                        let (got, dups) = run(&program, cfg.clone().with_threads(threads));
                        let missing: Vec<_> = reference.difference(&got).cloned().collect();
                        let extra: Vec<_> = got.difference(&reference).cloned().collect();
                        if !missing.is_empty() || !extra.is_empty() || dups > 0 {
                            divergences += 1;
                            eprintln!(
                                "DIVERGENCE case={case} prio={priorities:?} order={order:?} \
                                 threads={threads} missing={} extra={} dups={dups}\n{:?}",
                                missing.len(),
                                extra.len(),
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
    println!("LEGACYDIFF seed={seed:#x} progs={progs} terminals={terminals} divergences={divergences}");
    assert_eq!(divergences, 0, "legacy certified pruning diverged");
}
