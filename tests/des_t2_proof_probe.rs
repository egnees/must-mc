//! Independent bounded falsification searches for the existing DES + T2 regime.
//! A passing corpus is evidence only for its concrete cases, never a proof.
//! Reproduce/extend with T2_PROOF_CASES and T2_PROOF_SECONDS (default 300 / 30).

mod common;
mod hunt_common;

use std::collections::BTreeSet;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use hunt_common::{Op, Rng, Sel, VdProgram};
use must::{
    explore, Config, EventId, Execution, ExecutionGraph, ExecutionKind, Label, Model, Observer,
    Program, ThreadNext, Val,
};

#[derive(Clone, Debug)]
struct FutureMode {
    program: VdProgram,
    summarize: bool,
}

impl Program for FutureMode {
    fn num_threads(&self) -> usize {
        self.program.num_threads()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        self.program.next(traces)
    }
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        if self.summarize {
            self.program.possible_future(tid, trace)
        } else {
            None
        }
    }
}

type Keys = BTreeSet<(u8, String)>;

struct Audit {
    keys: Mutex<Keys>,
    records: AtomicUsize,
    visits: AtomicUsize,
    nd_revisits: AtomicUsize,
    nb_revisits: AtomicUsize,
    viable_calls: AtomicUsize,
    viable_false: AtomicUsize,
    capture_send: bool,
    last_send: Mutex<Option<ExecutionGraph>>,
    started: Instant,
}

impl Default for Audit {
    fn default() -> Self {
        Self {
            keys: Mutex::new(BTreeSet::new()),
            records: AtomicUsize::new(0),
            visits: AtomicUsize::new(0),
            nd_revisits: AtomicUsize::new(0),
            nb_revisits: AtomicUsize::new(0),
            viable_calls: AtomicUsize::new(0),
            viable_false: AtomicUsize::new(0),
            capture_send: false,
            last_send: Mutex::new(None),
            started: Instant::now(),
        }
    }
}

#[derive(Debug)]
struct SearchLimit;

impl Observer for Audit {
    fn on_event_added(&self, graph: &ExecutionGraph, event: EventId) {
        if self.capture_send && matches!(graph.label(event), Label::Send { .. }) {
            *self.last_send.lock().unwrap() = Some(graph.clone());
        }
    }
    fn on_visit_enter(&self, _g: &ExecutionGraph) {
        let visits = self.visits.fetch_add(1, Ordering::Relaxed) + 1;
        if visits > 100_000
            || (visits % 128 == 0 && self.started.elapsed() > Duration::from_secs(2))
        {
            std::panic::panic_any(SearchLimit);
        }
    }
    fn on_execution(&self, execution: &Execution, kind: ExecutionKind) {
        assert!(
            must::check(execution.graph()).is_feasible(),
            "time-infeasible reported terminal"
        );
        let kind = match kind {
            ExecutionKind::Full => 0,
            ExecutionKind::Blocked => 1,
            ExecutionKind::Error => 2,
        };
        self.records.fetch_add(1, Ordering::Relaxed);
        self.keys
            .lock()
            .unwrap()
            .insert((kind, execution.canonical_key()));
    }
    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        _r: EventId,
        _s: EventId,
        deleted: &BTreeSet<EventId>,
    ) {
        if deleted
            .iter()
            .any(|&e| matches!(g.label(e), Label::Nondet { .. }))
        {
            self.nd_revisits.fetch_add(1, Ordering::Relaxed);
        }
        if deleted
            .iter()
            .any(|&e| g.label(e).blocking() == Some(false) && !g.reads_bottom(e))
        {
            self.nb_revisits.fetch_add(1, Ordering::Relaxed);
        }
    }
    fn on_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _v: Val,
        _s: EventId,
        _label: &Label,
        verdict: bool,
    ) {
        self.viable_calls.fetch_add(1, Ordering::Relaxed);
        self.viable_false
            .fetch_add(usize::from(!verdict), Ordering::Relaxed);
    }
}

#[derive(Default)]
struct Coverage {
    completed: usize,
    skipped: usize,
    runs: usize,
    visits: usize,
    nd_revisits: usize,
    nb_revisits: usize,
    viable_calls: usize,
    viable_false: usize,
}

fn compare(
    program: &VdProgram,
    priorities: &[usize],
    context: &str,
    coverage: &mut Coverage,
) -> bool {
    let base = Config::default()
        .collect_errors()
        .with_priorities(priorities.to_vec());
    let modes = [
        ("T1", false, base.clone().with_time_filter()),
        ("DES", false, base.clone().with_time_zombie()),
        ("T2 future", true, base.clone().with_time_predicate()),
        ("T2 unknown", false, base.with_time_predicate()),
    ];
    let mut reference: Option<Keys> = None;
    for (name, summarize, config) in modes {
        let wrapped = FutureMode {
            program: program.clone(),
            summarize,
        };
        let audit = Audit {
            capture_send: !context.starts_with("seed="),
            ..Audit::default()
        };
        match catch_unwind(AssertUnwindSafe(|| {
            explore(|| wrapped.clone(), &audit, config)
        })) {
            Ok(()) => {}
            Err(reason) if reason.is::<SearchLimit>() => {
                coverage.skipped += 1;
                return false;
            }
            Err(reason) => {
                let message = reason
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| reason.downcast_ref::<&str>().copied())
                    .unwrap_or("non-string panic");
                let partial = audit.keys.lock().unwrap();
                let missing = reference
                    .as_ref()
                    .map(|expected| expected.difference(&partial).count());
                let extra = reference
                    .as_ref()
                    .map(|expected| partial.difference(expected).count());
                let trace = audit
                    .last_send
                    .lock()
                    .unwrap()
                    .as_ref()
                    .map(|g| {
                        format!(
                            "latest_send_feasible={} stamps={:?}\n{}",
                            must::check(g).is_feasible(),
                            g.iter_events().map(|e| (e, g.stamp(e))).collect::<Vec<_>>(),
                            g.canonical_key()
                        )
                    })
                    .unwrap_or_default();
                panic!("{context} {name} @{priorities:?}: explorer panic: {message}\naccepted_before_panic={} missing={missing:?} extra={extra:?}\n{trace}\n{program:#?}", partial.len());
            }
        }
        let actual = audit.keys.into_inner().unwrap();
        if context.starts_with("six-thread") {
            println!(
                "{context} {name}: distinct={} recorded={} visits={}",
                actual.len(),
                audit.records.load(Ordering::Relaxed),
                audit.visits.load(Ordering::Relaxed)
            );
        }
        assert_eq!(
            audit.records.load(Ordering::Relaxed),
            actual.len(),
            "{context} {name} @{priorities:?}: DUPLICATES\n{program:#?}"
        );
        if let Some(expected) = &reference {
            assert_eq!(
                &actual, expected,
                "{context} {name} @{priorities:?}: TERMINAL-SET DIVERGENCE\n{program:#?}"
            );
        } else {
            reference = Some(actual);
        }
        coverage.runs += 1;
        coverage.visits += audit.visits.load(Ordering::Relaxed);
        if name.starts_with("T2") {
            coverage.nd_revisits += audit.nd_revisits.load(Ordering::Relaxed);
            coverage.nb_revisits += audit.nb_revisits.load(Ordering::Relaxed);
            coverage.viable_calls += audit.viable_calls.load(Ordering::Relaxed);
            coverage.viable_false += audit.viable_false.load(Ordering::Relaxed);
        }
    }
    coverage.completed += 1;
    true
}

fn window(rng: &mut Rng) -> (u64, u64) {
    match rng.below(5) {
        0 => (0, 12),
        1 => (0, rng.below(3) as u64),
        2 => {
            let lo = 4 + rng.below(6) as u64;
            (lo, lo + rng.below(3) as u64)
        }
        _ => {
            let lo = rng.below(6) as u64;
            (lo, lo + rng.below(5) as u64)
        }
    }
}

fn random_program(seed: u64) -> VdProgram {
    let mut rng = Rng::new(seed);
    let n = 3 + rng.below(3);
    let mut threads = Vec::new();
    let mut nd_left = 2;
    for tid in 0..n {
        let count = 2 + rng.below(4);
        let mut events = Vec::new();
        let mut guards = Vec::new();
        for index in 0..count {
            let roll = rng.below(100);
            let op = if tid == 0 && index == 0 {
                Op::Recv {
                    sel: Sel::Any,
                    blocking: false,
                }
            } else if roll < 35 {
                let sel = if !guards.is_empty() && rng.chance(25) {
                    Sel::EqGuard(rng.pick(&guards))
                } else if rng.chance(50) {
                    Sel::Any
                } else {
                    Sel::Eq(rng.pick(&["a", "b", "c"]))
                };
                Op::Recv {
                    sel,
                    blocking: rng.chance(65),
                }
            } else if roll < 43 && nd_left > 0 {
                nd_left -= 1;
                if rng.chance(30) {
                    Op::Nondet3
                } else {
                    Op::Nondet
                }
            } else {
                let dst = if rng.chance(40) { 0 } else { rng.below(n) };
                let model = if rng.chance(40) {
                    Model::P2p
                } else {
                    Model::Asyn
                };
                let val = rng.pick(&["a", "b", "c"]);
                let (lo, hi) = window(&mut rng);
                if !guards.is_empty() && rng.chance(55) {
                    let guard = rng.pick(&guards);
                    let eq = rng.pick(&["a", "b", "c"]);
                    if rng.chance(50) {
                        Op::SendIf {
                            guard,
                            eq,
                            dst,
                            model,
                            val,
                            lo,
                            hi,
                        }
                    } else {
                        let (lo2, hi2) = window(&mut rng);
                        Op::SendWin {
                            guard,
                            eq,
                            dst,
                            model,
                            val,
                            lo1: lo,
                            hi1: hi,
                            lo2,
                            hi2,
                        }
                    }
                } else {
                    Op::Send {
                        dst,
                        model,
                        val,
                        lo,
                        hi,
                    }
                }
            };
            if matches!(op, Op::Recv { .. } | Op::Nondet | Op::Nondet3) {
                guards.push(index);
            }
            events.push(op);
        }
        threads.push(events);
    }
    VdProgram { threads }
}

#[test]
#[ignore = "explicit bounded falsification corpus; empirical coverage is not a proof"]
fn seeded_mixed_models_and_future_precision() {
    let cases = std::env::var("T2_PROOF_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);
    let seconds = std::env::var("T2_PROOF_SECONDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);
    let started = Instant::now();
    let mut coverage = Coverage::default();
    let mut tested = 0;
    for case in 0..cases {
        if started.elapsed() > Duration::from_secs(seconds) {
            break;
        }
        let seed = 0x000d_3572_2026_u64.wrapping_add(case * 0x10001);
        let program = random_program(seed);
        let n = program.num_threads();
        let mut rotated = (0..n).collect::<Vec<_>>();
        rotated.rotate_left(1);
        for priorities in [(0..n).collect::<Vec<_>>(), (0..n).rev().collect(), rotated] {
            compare(
                &program,
                &priorities,
                &format!("seed={seed:#x} case={case}"),
                &mut coverage,
            );
        }
        tested += 1;
    }
    println!("tested={tested} completed={} skipped={} runs={} visits={} nd_deleted_revisits={} nb_nonbottom_deleted_revisits={} viable_calls={} viable_false={} elapsed={:.3}s",
        coverage.completed, coverage.skipped, coverage.runs, coverage.visits,
        coverage.nd_revisits, coverage.nb_revisits, coverage.viable_calls, coverage.viable_false,
        started.elapsed().as_secs_f64());
    assert!(tested > 0);
}

fn six_thread_program() -> VdProgram {
    use hunt_common::{brecv, send};
    VdProgram {
        threads: vec![
            vec![brecv(Sel::Any)],
            vec![send(0, "a", 0, 100), send(0, "b", 10, 10)],
            vec![brecv(Sel::Eq("g")), send(0, "early", 0, 0)],
            vec![send(2, "g", 5, 5)],
            vec![brecv(Sel::Eq("q")), Op::Nondet],
            vec![send(4, "q", 3, 3)],
        ],
    }
}

#[test]
#[ignore = "historical self-witness failure; opt-in exact-set regression after diagnostic repair"]
fn six_thread_nondet_self_witness() {
    let program = six_thread_program();
    let mut coverage = Coverage::default();
    assert!(compare(
        &program,
        &[0, 1, 2, 3, 4, 5],
        "six-thread nondet",
        &mut coverage
    ));
}

#[test]
#[ignore = "historical interrupted branch; opt-in exact-set regression after diagnostic repair"]
fn six_thread_outer_nondet_incompleteness() {
    let mut program = six_thread_program();
    program.threads[1].insert(0, Op::Nondet);
    let mut coverage = Coverage::default();
    assert!(compare(
        &program,
        &[0, 1, 2, 3, 4, 5],
        "six-thread outer nondet",
        &mut coverage
    ));
}

#[test]
#[ignore = "historical three-thread self-witness failure; opt-in exact-set regression"]
fn three_thread_nondet_self_witness() {
    use hunt_common::{brecv, send};
    let program = VdProgram {
        threads: vec![
            vec![send(0, "a", 0, 10), send(0, "b", 10, 10), brecv(Sel::Any)],
            vec![
                send(1, "g", 5, 5),
                brecv(Sel::Eq("g")),
                send(0, "early", 0, 0),
            ],
            vec![send(2, "q", 3, 3), brecv(Sel::Eq("q")), Op::Nondet],
        ],
    };
    let mut coverage = Coverage::default();
    assert!(compare(
        &program,
        &[0, 1, 2],
        "three-thread nondet",
        &mut coverage
    ));
}

fn two_thread_program(outer_nondet: bool) -> VdProgram {
    use hunt_common::{brecv, send};
    let mut program = VdProgram {
        threads: vec![
            vec![
                send(0, "a", 1, 4),
                send(0, "b", 4, 4),
                brecv(Sel::Any),
                Op::Nondet,
            ],
            vec![
                send(1, "g", 1, 1),
                brecv(Sel::Eq("g")),
                send(0, "early", 1, 1),
            ],
        ],
    };
    if outer_nondet {
        program.threads[0].insert(0, Op::Nondet);
    }
    program
}

#[test]
#[ignore = "historical two-thread self-witness failure; opt-in exact-set regression"]
fn two_thread_nondet_self_witness() {
    let program = two_thread_program(false);
    let mut coverage = Coverage::default();
    assert!(compare(
        &program,
        &[0, 1],
        "two-thread nondet",
        &mut coverage
    ));
}

#[test]
#[ignore = "historical two-thread interrupted branch; opt-in exact-set regression"]
fn two_thread_outer_nondet_incompleteness() {
    let program = two_thread_program(true);
    let mut coverage = Coverage::default();
    assert!(compare(
        &program,
        &[0, 1],
        "two-thread outer nondet",
        &mut coverage
    ));
}

#[test]
fn two_thread_positive_windows_independent_temporal_reference() {
    let program = two_thread_program(false);
    let collector = must::ExecutionCollector::new();
    explore(
        || program.clone(),
        &collector,
        Config::default().collect_errors(),
    );
    assert_eq!(
        collector.full_count(),
        6,
        "three receive sources times two nondet choices"
    );
    let mut feasible = 0;
    for terminal in collector.full() {
        let actual = common::time_feasible_ref(terminal.graph(), &mut 100)
            .expect("only the a-send has four possible integral delays");
        assert_eq!(actual, must::check(terminal.graph()).is_feasible());
        feasible += usize::from(actual);
    }
    assert_eq!(
        feasible, 4,
        "a or early can be consumed; b at4 loses to early at2"
    );
}
