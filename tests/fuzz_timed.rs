//! Deterministic differential fuzzing of the eager-time filter (engine_plan §5.в).
//!
//! Like `fuzz.rs`, but every send carries a finite delivery window and the explorer runs
//! under `Config::with_time_filter().collect_errors()`. For each random program the
//! explorer's terminal partition — *realizable* (full ∪ blocked) vs *filtered*
//! (time-infeasible) — is diffed against a fully independent reference:
//!
//!   * the untimed terminal set is enumerated by the same brute force as `fuzz.rs`
//!     (every consistent maximal prefix / full graph), then
//!   * each terminal graph is classified by `common::time_feasible_ref`, an integer
//!     delay-vector enumeration written straight from engine_plan §0 — it never touches
//!     `must::time`, so a bug shared by the solver and this reference is vanishingly
//!     unlikely.
//!
//! Asserted per program × priority permutation:
//!   1. the explorer's *realizable* terminal keys equal the reference's time-feasible set;
//!   2. its *filtered* keys equal the reference's time-infeasible set (the partition check);
//!   3. no duplicate terminal or filtered keys;
//!   4. both partitions are invariant to the priority permutation.
//!
//! Models are restricted to `{Asyn, P2p}` (the only timed-supported models, Б3) and every
//! window is finite, so the integer reference is a valid, terminating oracle.

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::{permutations, time_feasible_ref, SeqProgram};
use must::event::{Label, Model, Pred, Val, Window};
use must::graph::ExecutionGraph;
use must::{consistent, explore, Config, CountingObserver, ExecutionCollector};

/// rf-iteration budget for one program's untimed brute force (mirrors `fuzz.rs`).
const BRUTE_FORCE_BUDGET: usize = 400_000;
/// Delay-vector budget for one program's integer time reference (across all its terminals).
const TIME_BUDGET: usize = 2_000_000;

/// A set of canonical execution keys.
type KeySet = BTreeSet<String>;
/// The reference partition of the untimed terminals: (feasible-full, feasible-terminal,
/// infeasible-terminal) key sets.
type TimePartition = (KeySet, KeySet, KeySet);
/// The per-program invariance reference: partition (full, terminal, filtered) plus the
/// filtered count from the first permutation.
type PriorityRef = (KeySet, KeySet, KeySet, usize);

/// SplitMix64, so the corpus is reproducible with no external crate (copy of `fuzz.rs`).
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }
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

/// A finite delivery window, drawn from four narrow/wide bands. Never ∞, so the integer
/// reference stays enumerable (Б3).
///
/// Two of the bands are deliberately *separated* — an early `[0, 0..=1]` and a late
/// `[3..=5, +0..=1]` — so that when both land on one receiver, reading the late one is
/// filtered (its early competitor has `hi < lo`, and a `lo = 0` reading escapes via the
/// A-clause). Without such separation a random narrow/wide mix almost never makes the
/// filter bite, leaving the corpus degenerate. The remaining bands (a mid-narrow window
/// and the wide `[0, 6]`) keep plenty of overlapping, *un*filtered timed readings too.
fn timed_window(rng: &mut Rng) -> Window {
    match rng.below(4) {
        0 => Window::new(0, rng.below(2) as u64), // early [0, 0..=1]
        1 => {
            let lo = 3 + rng.below(3) as u64; // late [3..=5, +0..=1]
            Window::new(lo, lo + rng.below(2) as u64)
        }
        2 => Window::new(0, 6), // wide
        _ => {
            let lo = rng.below(4) as u64; // mid-narrow [0..=3, +0..=2]
            Window::new(lo, lo + rng.below(3) as u64)
        }
    }
}

/// Generate one random timed straight-line program: 2-4 threads, 1-3 events each; ~50%
/// sends (each with a finite window and an Asyn/P2p model), ~40% receives (~1/3
/// non-blocking), ~10% nondet. Same shape as `fuzz.rs::gen_program`, restricted to the
/// timed-supported models with windows added.
fn gen_program(rng: &mut Rng) -> SeqProgram {
    let models = [Model::Asyn, Model::P2p];
    let vals = ["a", "b"];
    let nt = 2 + rng.below(3);
    let mut threads = Vec::with_capacity(nt);
    for _ in 0..nt {
        let ne = 1 + rng.below(3);
        let mut evs = Vec::with_capacity(ne);
        for _ in 0..ne {
            let roll = rng.below(10);
            if roll < 5 {
                // Bias destinations onto the last thread so several sends land on one
                // receiver — the structural precondition for a *competitor*, and hence for a
                // filtered reading. Without this the filter almost never bites (a random dst
                // spreads sends too thin across threads).
                let dst = if rng.below(2) == 0 {
                    nt - 1
                } else {
                    rng.below(nt)
                };
                let val = vals[rng.below(vals.len())];
                let model = models[rng.below(models.len())];
                evs.push(Label::send_within(model, dst, val, timed_window(rng)));
            } else if roll < 9 {
                let pred = if rng.below(2) == 0 {
                    Pred::eq(vals[rng.below(vals.len())])
                } else {
                    Pred::any()
                };
                if rng.below(3) == 0 {
                    evs.push(Label::recv_nb(pred));
                } else {
                    evs.push(Label::recv(pred));
                }
            } else {
                let set: &[&str] = if rng.below(2) == 0 {
                    &["a"]
                } else {
                    &["a", "b"]
                };
                evs.push(Label::nondet(set.iter().copied()));
            }
        }
        threads.push(evs);
    }
    SeqProgram::new(threads)
}

/// Whether prefix graph `g` (per-thread lengths `lens`) is maximal (copy of `fuzz.rs`).
fn is_maximal(prog: &SeqProgram, g: &ExecutionGraph, lens: &[usize], full_len: &[usize]) -> bool {
    let unread = g.unread_sends();
    for (t, thread) in prog.threads.iter().enumerate() {
        if lens[t] == full_len[t] {
            continue;
        }
        match &thread[lens[t]] {
            Label::Recv {
                blocking: true,
                pred,
            } => {
                let addable = unread.iter().any(|&s| {
                    g.label(s).dst() == Some(t) && pred.test(g.label(s).val().unwrap_or(""))
                });
                if addable {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// Brute-force the untimed terminal set of `prog`, keyed by canonical key, each with its
/// graph and whether it is a *full* terminal. `None` if over [`BRUTE_FORCE_BUDGET`]. This
/// is `fuzz.rs::brute_force_terminals` extended to hand back the graphs (the time reference
/// needs them).
fn brute_force_terminal_graphs(
    prog: &SeqProgram,
) -> Option<BTreeMap<String, (ExecutionGraph, bool)>> {
    let nt = prog.threads.len();
    let full_len: Vec<usize> = prog.threads.iter().map(Vec::len).collect();

    let stops: Vec<Vec<usize>> = prog
        .threads
        .iter()
        .map(|evs| {
            let mut v: Vec<usize> = evs
                .iter()
                .enumerate()
                .filter(|(_, l)| matches!(l, Label::Recv { blocking: true, .. }))
                .map(|(i, _)| i)
                .collect();
            v.push(evs.len());
            v.sort_unstable();
            v.dedup();
            v
        })
        .collect();

    let mut out: BTreeMap<String, (ExecutionGraph, bool)> = BTreeMap::new();
    let mut budget = BRUTE_FORCE_BUDGET;

    let mut sc = vec![0usize; nt];
    loop {
        let lens: Vec<usize> = (0..nt).map(|t| stops[t][sc[t]]).collect();

        let mut base = ExecutionGraph::new();
        let mut recvs = Vec::new();
        let mut nds = Vec::new();
        for (t, &len) in lens.iter().enumerate() {
            for i in 0..len {
                let e = base.add_event(t, prog.threads[t][i].clone());
                if prog.threads[t][i].is_recv() {
                    recvs.push(e);
                } else if prog.threads[t][i].is_nondet() {
                    nds.push(e);
                }
            }
        }
        let sends = base.sends();
        let k = recvs.len();
        let m = nds.len();

        let nd_sets: Vec<Vec<Val>> = nds
            .iter()
            .map(|&e| base.label(e).nd_set().expect("nondet event").to_vec())
            .collect();
        let mut opts: Vec<usize> = recvs
            .iter()
            .map(|&r| {
                let nb = matches!(
                    base.label(r),
                    Label::Recv {
                        blocking: false,
                        ..
                    }
                );
                sends.len() + usize::from(nb)
            })
            .collect();
        opts.extend(nd_sets.iter().map(Vec::len));
        let dims = k + m;

        let iters: usize = opts.iter().try_fold(1usize, |a, &o| a.checked_mul(o))?;
        budget = budget.checked_sub(iters.max(1))?;

        if iters > 0 {
            let mut choice = vec![0usize; dims];
            loop {
                let mut g = base.clone();
                for (i, &r) in recvs.iter().enumerate() {
                    let src = sends.get(choice[i]).copied();
                    g.set_rf(r, src);
                }
                for (j, &e) in nds.iter().enumerate() {
                    g.set_nd(e, nd_sets[j][choice[k + j]]);
                }
                if consistent(&g) && is_maximal(prog, &g, &lens, &full_len) {
                    let is_full = lens == full_len;
                    let key = g.canonical_key();
                    out.entry(key).or_insert((g, is_full));
                }
                if dims == 0 {
                    break;
                }
                let mut i = 0;
                loop {
                    if i == dims {
                        break;
                    }
                    choice[i] += 1;
                    if choice[i] < opts[i] {
                        break;
                    }
                    choice[i] = 0;
                    i += 1;
                }
                if i == dims {
                    break;
                }
            }
        }

        let mut t = 0;
        loop {
            if t == nt {
                return Some(out);
            }
            sc[t] += 1;
            if sc[t] < stops[t].len() {
                break;
            }
            sc[t] = 0;
            t += 1;
        }
    }
}

/// Partition the untimed terminals into (time-feasible full, time-feasible terminal,
/// time-infeasible terminal) canonical-key sets via the independent integer reference.
/// `None` if the reference exceeds [`TIME_BUDGET`] on any terminal.
fn time_partition(graphs: &BTreeMap<String, (ExecutionGraph, bool)>) -> Option<TimePartition> {
    let mut budget = TIME_BUDGET;
    let mut feas_full = BTreeSet::new();
    let mut feas_term = BTreeSet::new();
    let mut infeas = BTreeSet::new();
    for (key, (g, is_full)) in graphs {
        if time_feasible_ref(g, &mut budget)? {
            feas_term.insert(key.clone());
            if *is_full {
                feas_full.insert(key.clone());
            }
        } else {
            infeas.insert(key.clone());
        }
    }
    Some((feas_full, feas_term, infeas))
}

fn graph_has_nb_recv(g: &ExecutionGraph) -> bool {
    g.recvs()
        .into_iter()
        .any(|r| g.label(r).blocking() == Some(false))
}

fn graph_has_blocking_read(g: &ExecutionGraph) -> bool {
    g.recvs()
        .into_iter()
        .any(|r| g.label(r).blocking() == Some(true) && g.reads_from(r).is_some())
}

/// Whether some `(tid, dst)` channel carries both an Asyn and a P2p send (И1 mixing).
fn has_mixed_channel(prog: &SeqProgram) -> bool {
    let mut chans: BTreeMap<(usize, usize), (bool, bool)> = BTreeMap::new();
    for (t, thread) in prog.threads.iter().enumerate() {
        for l in thread {
            if let (Some(m), Some(d)) = (l.model(), l.dst()) {
                let e = chans.entry((t, d)).or_default();
                match m {
                    Model::Asyn => e.0 = true,
                    Model::P2p => e.1 = true,
                    _ => {}
                }
            }
        }
    }
    chans.values().any(|&(a, p)| a && p)
}

/// Per-program statistics for the corpus non-degeneracy checks.
#[derive(Default)]
struct ProgStats {
    /// Whether the time reference stayed within budget (so the partition asserts ran).
    time_cross_checked: bool,
    /// Whether the filter suppressed at least one terminal.
    filtered: bool,
    /// Whether some terminal graph has both a non-blocking receive and a (timed) send.
    nb_in_timed: bool,
    /// Whether some terminal graph has a blocking receive reading a timed send.
    blocking_read: bool,
    /// Whether some `(tid, dst)` channel mixes Asyn and P2p sends.
    mixed_channel: bool,
}

/// Diff the explorer against the reference for one program, over every priority
/// permutation, and collect its statistics.
fn check_program(case: usize, prog: &SeqProgram) -> ProgStats {
    let nt = prog.threads.len();
    let graphs = brute_force_terminal_graphs(prog);
    let partition = graphs.as_ref().and_then(time_partition);

    let mut stats = ProgStats {
        time_cross_checked: partition.is_some(),
        mixed_channel: has_mixed_channel(prog),
        ..Default::default()
    };

    let mut reference: Option<PriorityRef> = None;

    for (pi, perm) in permutations(nt).into_iter().enumerate() {
        let obs = (CountingObserver::new(), ExecutionCollector::new());
        explore(
            || prog.clone(),
            &obs,
            Config::default()
                .collect_errors()
                .with_time_filter()
                .with_priorities(perm.clone()),
        );
        let (cnt, col) = &obs;

        let full: BTreeSet<String> = col.full_keys().into_iter().collect();
        let term_vec = col.terminal_keys();
        let term: BTreeSet<String> = term_vec.iter().cloned().collect();
        let filt_vec = col.filtered_keys();
        let filt: BTreeSet<String> = filt_vec.iter().cloned().collect();

        // (3) no duplicate realizable / filtered terminals.
        assert_eq!(
            term_vec.len(),
            term.len(),
            "case {case} perm {perm:?}: duplicate realizable terminals\n{:#?}",
            prog.threads
        );
        assert_eq!(
            filt_vec.len(),
            filt.len(),
            "case {case} perm {perm:?}: duplicate filtered terminals\n{:#?}",
            prog.threads
        );

        // (1)+(2) the realizable/filtered partition matches the independent reference.
        if let Some((rf_full, rf_term, rf_infeas)) = &partition {
            assert_eq!(
                &full, rf_full,
                "case {case} perm {perm:?}: realizable full keys disagree with the time reference\n{:#?}",
                prog.threads
            );
            assert_eq!(
                &term, rf_term,
                "case {case} perm {perm:?}: realizable terminal keys disagree with the time reference\n{:#?}",
                prog.threads
            );
            assert_eq!(
                &filt, rf_infeas,
                "case {case} perm {perm:?}: filtered keys disagree with the time reference\n{:#?}",
                prog.threads
            );
        }

        // (4) both partitions and the filtered count are priority-invariant.
        match &reference {
            None => {
                if pi == 0 {
                    let mut all = col.full();
                    all.extend(col.blocked());
                    let filtered_graphs: Vec<ExecutionGraph> = col
                        .filtered()
                        .into_iter()
                        .map(|(e, _)| e.graph().clone())
                        .collect();
                    let terminal_graphs: Vec<&ExecutionGraph> = all
                        .iter()
                        .map(|e| e.graph())
                        .chain(filtered_graphs.iter())
                        .collect();
                    stats.filtered = cnt.filtered() > 0;
                    stats.nb_in_timed = terminal_graphs
                        .iter()
                        .any(|g| graph_has_nb_recv(g) && !g.sends().is_empty());
                    stats.blocking_read =
                        terminal_graphs.iter().any(|g| graph_has_blocking_read(g));
                }
                reference = Some((full, term, filt, cnt.filtered()));
            }
            Some((rf, rt, ri, rc)) => {
                assert_eq!(
                    &full, rf,
                    "case {case} perm {perm:?}: realizable full set varies with priority\n{:#?}",
                    prog.threads
                );
                assert_eq!(
                    &term, rt,
                    "case {case} perm {perm:?}: realizable terminal set varies with priority\n{:#?}",
                    prog.threads
                );
                assert_eq!(
                    &filt, ri,
                    "case {case} perm {perm:?}: filtered set varies with priority\n{:#?}",
                    prog.threads
                );
                assert_eq!(
                    cnt.filtered(),
                    *rc,
                    "case {case} perm {perm:?}: filtered count varies with priority\n{:#?}",
                    prog.threads
                );
            }
        }
    }

    // -- G1-accept: the full T2 predicate search on the same program (T2_PLAN §5б). ----------
    //
    // The predicate order is a pure function of the graph (priority-independent), so one run
    // suffices; we assert it against the same independent reference the T1 filter is checked on,
    // plus the two T2-only invariants: no duplicate keys and — since a SeqProgram has an exact
    // `possible_future`, so `forced_closure` is exact — **zero** dead branches (optimality-b).
    check_program_predicate(case, prog, partition.as_ref());

    // -- Zombie == T1-filter (T2_ORACLE_SPEC §2.2 point 1): the untimed algorithm under the DES
    // order must reproduce the T1-filter partition EXACTLY — both the realizable and the
    // filtered key sets. This isolates `pick_des` as a valid next_P policy, decoupled from the
    // whole T2 machinery. Zombie is priority-invariant by construction (pick_des ignores
    // priorities), so one run suffices; it is diffed against the T1 sets of the first
    // permutation (themselves asserted priority-invariant above).
    if let Some((rf_full, rf_term, rf_filt, _)) = &reference {
        check_program_zombie(case, prog, rf_full, rf_term, rf_filt);
    }

    stats
}

/// Run `prog` under `Config::with_time_zombie` and assert its partition equals the T1-filter's.
fn check_program_zombie(
    case: usize,
    prog: &SeqProgram,
    rf_full: &KeySet,
    rf_term: &KeySet,
    rf_filt: &KeySet,
) {
    let col = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &col,
        Config::default().collect_errors().with_time_zombie(),
    );

    let full: BTreeSet<String> = col.full_keys().into_iter().collect();
    let term_vec = col.terminal_keys();
    let term: BTreeSet<String> = term_vec.iter().cloned().collect();
    let filt_vec = col.filtered_keys();
    let filt: BTreeSet<String> = filt_vec.iter().cloned().collect();

    // No duplicates (Theorem 4.1 verbatim under the DES policy).
    assert_eq!(
        term_vec.len(),
        term.len(),
        "case {case}: zombie produced duplicate realizable terminals\n{:#?}",
        prog.threads
    );
    assert_eq!(
        filt_vec.len(),
        filt.len(),
        "case {case}: zombie produced duplicate filtered terminals\n{:#?}",
        prog.threads
    );

    // Exact partition match against T1-filter.
    assert_eq!(
        &full, rf_full,
        "case {case}: zombie full keys differ from T1-filter\n{:#?}",
        prog.threads
    );
    assert_eq!(
        &term, rf_term,
        "case {case}: zombie realizable terminal keys differ from T1-filter\n{:#?}",
        prog.threads
    );
    assert_eq!(
        &filt, rf_filt,
        "case {case}: zombie filtered keys differ from T1-filter\n{:#?}",
        prog.threads
    );
}

/// Run `prog` under `Config::with_time_predicate` and assert the G1-accept invariants.
fn check_program_predicate(case: usize, prog: &SeqProgram, partition: Option<&TimePartition>) {
    let obs = (
        ExecutionCollector::new(),
        must::DeadBranchDetector::new(),
    );
    explore(
        || prog.clone(),
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let (col, dead) = &obs;

    // (2) optimality-(a): no duplicate realizable terminals.
    let term_vec = col.terminal_keys();
    let term: BTreeSet<String> = term_vec.iter().cloned().collect();
    assert_eq!(
        term_vec.len(),
        term.len(),
        "case {case}: T2 produced duplicate realizable terminals\n{:#?}",
        prog.threads
    );

    // (3) optimality-(b): no dead Visit nodes (exact forced_closure on a SeqProgram).
    assert_eq!(
        dead.dead(),
        0,
        "case {case}: T2 has {} dead Visit nodes (of {}) — a forced-closure over-/under-gate\n{:#?}",
        dead.dead(),
        dead.visits(),
        prog.threads
    );

    // (1) completeness + no-loss: the T2 realizable set equals the independent reference
    // (full+blocked feasible terminals), whenever the reference stayed within budget.
    if let Some((rf_full, rf_term, _rf_infeas)) = partition {
        let full: BTreeSet<String> = col.full_keys().into_iter().collect();
        assert_eq!(
            &full, rf_full,
            "case {case}: T2 realizable full keys disagree with the time reference\n{:#?}",
            prog.threads
        );
        assert_eq!(
            &term, rf_term,
            "case {case}: T2 realizable terminal keys disagree with the time reference\n{:#?}",
            prog.threads
        );
    }
}

/// Aggregate statistics of a corpus run.
#[derive(Default)]
struct CorpusStats {
    progs: usize,
    time_cross_checked: usize,
    with_filtered: usize,
    with_timed_no_filter: usize,
    with_nb_in_timed: usize,
    with_mixed_channel: usize,
}

fn run_corpus(seed: u64, n_progs: usize) -> CorpusStats {
    let mut rng = Rng::new(seed);
    let mut stats = CorpusStats {
        progs: n_progs,
        ..Default::default()
    };
    for case in 0..n_progs {
        let prog = gen_program(&mut rng);
        let s = check_program(case, &prog);
        if s.time_cross_checked {
            stats.time_cross_checked += 1;
        }
        if s.filtered {
            stats.with_filtered += 1;
        }
        if s.blocking_read && !s.filtered {
            stats.with_timed_no_filter += 1;
        }
        if s.nb_in_timed {
            stats.with_nb_in_timed += 1;
        }
        if s.mixed_channel {
            stats.with_mixed_channel += 1;
        }
    }
    stats
}

/// Fast corpus for `cargo test`. Deterministic seed; ~150 programs.
#[test]
fn fuzz_timed_small_corpus() {
    let s = run_corpus(0x5EED_C0DE, 220);
    assert_eq!(s.progs, 220);
    // Non-degeneracy: the filter is exercised in both directions, non-blocking receives and
    // Asyn/P2p channel mixing all appear, and most programs are fully time-cross-checked.
    assert!(
        s.with_filtered >= 10,
        "too few programs with a filtered terminal ({}/150) — the time filter cuts nothing",
        s.with_filtered
    );
    assert!(
        s.with_timed_no_filter >= 10,
        "too few programs with a timed blocking read and nothing filtered ({}/150)",
        s.with_timed_no_filter
    );
    assert!(
        s.with_nb_in_timed >= 10,
        "too few programs with a non-blocking receive in a timed terminal graph ({}/150)",
        s.with_nb_in_timed
    );
    assert!(
        s.with_mixed_channel >= 5,
        "too few programs mixing Asyn and P2p on one channel ({}/150) — И1 undercovered",
        s.with_mixed_channel
    );
    assert!(
        s.time_cross_checked * 5 >= s.progs * 4,
        "too many programs exceeded the time-reference budget ({}/{})",
        s.time_cross_checked,
        s.progs
    );
}

/// Larger corpus, release-only (different seed for extra coverage).
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: 600-program timed fuzz corpus; run with --release"
)]
fn fuzz_timed_large_corpus() {
    let s = run_corpus(0xA11C_C0DE, 600);
    assert_eq!(s.progs, 600);
    assert!(s.with_filtered >= 30, "filtered {}/600", s.with_filtered);
    assert!(
        s.with_nb_in_timed >= 100,
        "nb_in_timed {}/600",
        s.with_nb_in_timed
    );
    assert!(
        s.with_mixed_channel >= 50,
        "mixed {}/600",
        s.with_mixed_channel
    );
}
