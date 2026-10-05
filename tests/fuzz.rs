//! Deterministic differential fuzzing: random straight-line programs, explorer vs a
//! brute-force reference over the **whole** terminal set [[P]]. A long-lived regression
//! that stresses the explorer far beyond the hand-picked oracles.
//!
//! ## What the brute-force reference covers
//!
//! [[P]] has two kinds of terminal execution, and the reference enumerates
//! *both*:
//!   * **Full executions** - every thread runs to completion, every receive reads a
//!     send, the graph is consistent.
//!   * **Blocked executions** - *maximal consistent prefixes* in which some thread is
//!     stuck on a blocking receive that has no matching unread send and cannot be
//!     consistently extended.
//!
//! The reference enumerates [[P]] by choosing, per thread, a *maximal-prefix boundary*
//! (finished, or just before one of the thread's blocking receives - never before a
//! send/error or a *non-blocking* receive, all of which would still be addable), and
//! every rf assignment over the included receives. Each receive's rf ranges over every
//! send, plus nothing for a **non-blocking** receive (`recv_timeout`) - and nothing may
//! be chosen by several non-blocking receives at once, exactly as in the DPOR. A blocking
//! receive cannot read nothing. A candidate is kept iff it is
//! `must::consistent` **and** maximal: every stopped thread's next receive has no
//! matching unread send. Maximality reuses the explorer's own addability rule
//! (scheduler.rs: a blocking receive is addable iff some unread send matches its
//! predicate/destination; a non-blocking receive is always addable), so the two sides
//! classify blocked vs extendable identically.
//!
//! ## What is asserted, per generated program
//!
//!   1. **Completeness + optimality of full executions.** The set of canonical keys of
//!      the explorer's *full* executions equals the reference's full set.
//!   2. **Completeness of the whole terminal set.** The set of canonical keys of the
//!      explorer's *terminal* executions (full union blocked) equals the reference's
//!      terminal set - this closes the earlier full-vs-blocked asymmetry: a
//!      priority-independent blocked-classification or blocked-completeness bug now fails
//!      the test.
//!   3. **No duplicates.** Terminal canonical keys are pairwise distinct under every
//!      priority permutation.
//!   4. **Priority invariance.** The set of terminal canonical keys, and the (full,
//!      blocked) counts, are identical across all priority permutations.
//!
//! Both sides use the same `must::consistent` predicate: the fuzzer validates the
//! *explorer* (its search completeness, optimality and terminal classification), not the
//! consistency predicate itself (that is `consistency.rs`'s job). Programs are
//! straight-line (value-independent), which is what makes the enumeration a valid oracle:
//! every thread's event sequence is fixed, so the only freedom is the prefix boundary, the
//! rf choice per receive, and the value of each nondet event - the reference
//! enumerates the last as an extra independent radix dimension, since a nondet value never
//! changes downstream events in a straight-line program.

mod common;

use std::collections::BTreeSet;

use common::{permutations, SeqProgram};
use must::event::{Label, Model, Pred, Val};
use must::graph::ExecutionGraph;
use must::{consistent, explore, Config, ExecutionCollector};

/// Total rf-iterations a single program's brute force may spend before it gives up and
/// returns `None` (the program is then checked only for dedup + invariance).
const BRUTE_FORCE_BUDGET: usize = 400_000;

/// Small deterministic PRNG (SplitMix64), so the fuzz corpus is reproducible with no
/// external crate.
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

/// Generate one random straight-line program: 2-4 threads, 1-3 events each, biased
/// toward sends (so the brute force stays tractable), random models and predicates. A
/// receive is non-blocking (`recv_timeout`) ~1/3 of the time; ~10% of events are a
/// nondet over a 1- or 2-value option set.
fn gen_program(rng: &mut Rng) -> SeqProgram {
    let models = [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox];
    let vals = ["a", "b"];
    let nt = 2 + rng.below(3); // 2..=4 threads
    let mut threads = Vec::with_capacity(nt);
    for _ in 0..nt {
        let ne = 1 + rng.below(3); // 1..=3 events
        let mut evs = Vec::with_capacity(ne);
        for _ in 0..ne {
            // ~50% sends, ~40% receives, ~10% nondet. Receives keep their old share so the
            // blocked / nothing-read corpus coverage is undisturbed.
            let roll = rng.below(10);
            if roll < 5 {
                let dst = rng.below(nt);
                let val = vals[rng.below(vals.len())];
                let model = models[rng.below(models.len())];
                evs.push(Label::send(model, dst, val));
            } else if roll < 9 {
                // Receive: selective (x == v) or any; ~1/3 non-blocking (can read nothing).
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
                // Nondet over {"a"} or {"a","b"} - a small extra multiplicative dimension.
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

/// Whether `g` - a prefix graph with per-thread lengths `lens` - is *maximal*: every
/// unfinished thread is genuinely blocked on its next (blocking) receive, i.e. that
/// receive has no matching unread send. Mirrors the explorer's addability
/// (scheduler.rs). `lens[t] < full_len[t]` is guaranteed by construction to point at a
/// blocking receive.
fn is_maximal(prog: &SeqProgram, g: &ExecutionGraph, lens: &[usize], full_len: &[usize]) -> bool {
    let unread = g.unread_sends();
    for (t, thread) in prog.threads.iter().enumerate() {
        if lens[t] == full_len[t] {
            continue; // finished
        }
        match &thread[lens[t]] {
            Label::Recv {
                blocking: true,
                pred,
                ..
            } => {
                let addable = unread.iter().any(|&s| {
                    g.label(s).dst() == Some(t) && pred.test(g.label(s).val().unwrap_or(""))
                });
                if addable {
                    return false; // could be extended - not maximal
                }
            }
            // Stop boundaries only ever fall on a blocking receive or the thread end.
            _ => return false,
        }
    }
    true
}

/// Brute-force reference for [[P]]: returns `(full_keys, terminal_keys)`, or `None` if the
/// enumeration would exceed [`BRUTE_FORCE_BUDGET`] rf-iterations. `terminal_keys` contains
/// `full_keys`; `full_keys` are the terminals in which every thread finished.
fn brute_force_terminals(prog: &SeqProgram) -> Option<(BTreeSet<String>, BTreeSet<String>)> {
    let nt = prog.threads.len();
    let full_len: Vec<usize> = prog.threads.iter().map(Vec::len).collect();

    // Per-thread stop boundaries: end (finished) + every blocking-receive index.
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

    let mut full_set = BTreeSet::new();
    let mut term_set = BTreeSet::new();
    let mut budget = BRUTE_FORCE_BUDGET;

    // Mixed-radix over stop-boundary choices (index into stops[t]).
    let mut sc = vec![0usize; nt];
    loop {
        let lens: Vec<usize> = (0..nt).map(|t| stops[t][sc[t]]).collect();

        // Build the prefix graph for this boundary combo.
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

        // One mixed-radix vector over all free choices: first the `k` receive rf options,
        // then the `m` nondet value options. A receive's options are every send plus
        // nothing for a non-blocking receive (a blocking receive cannot read nothing); a
        // nondet's options are its option-set values. Since the programs are straight-line,
        // a nondet value never changes downstream events - it is a pure multiplicative
        // dimension on the graph annotation, independent of the rf choices.
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

        // Number of assignments = product of every dimension's option count (empty
        // product = 1). A *blocking* receive with no matching source contributes 0,
        // zeroing the product - correct, since it cannot read nothing, so this boundary
        // combo yields no terminal. Nondet dimensions are >= 1 (option sets are non-empty).
        let iters: usize = opts.iter().try_fold(1usize, |a, &o| a.checked_mul(o))?;
        budget = budget.checked_sub(iters.max(1))?; // over budget -> None

        if iters > 0 {
            let mut choice = vec![0usize; dims];
            loop {
                let mut g = base.clone();
                for (i, &r) in recvs.iter().enumerate() {
                    // Option < sends.len() -> read that send; else nothing (non-blocking only).
                    let src = sends.get(choice[i]).copied();
                    g.set_rf(r, src);
                }
                for (j, &e) in nds.iter().enumerate() {
                    g.set_nd(e, nd_sets[j][choice[k + j]]);
                }
                if consistent(&g) && is_maximal(prog, &g, &lens, &full_len) {
                    let key = g.canonical_key();
                    if lens == full_len {
                        full_set.insert(key.clone());
                    }
                    term_set.insert(key);
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

        // Advance the stop-boundary combo.
        let mut t = 0;
        loop {
            if t == nt {
                return Some((full_set, term_set));
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

/// Outcome of checking one program.
struct ProgCheck {
    full: usize,
    blocked: usize,
    /// Whether the brute-force reference stayed within budget (so the exact-set asserts
    /// ran).
    brute_forced: bool,
    /// Whether any terminal execution has a receive reading nothing (a non-blocking timeout).
    has_bottom_read: bool,
}

/// Whether some collected terminal execution has a receive reading nothing.
fn any_bottom_read(col: &ExecutionCollector) -> bool {
    col.terminals().iter().any(|e| {
        let g = e.graph();
        g.recvs().into_iter().any(|r| g.reads_bottom(r))
    })
}

/// Per-program check.
fn check_program(case: usize, prog: &SeqProgram) -> ProgCheck {
    let n = prog.threads.len();
    let reference = brute_force_terminals(prog); // computed once
    let mut has_bottom_read = false;

    let mut ref_terminal: Option<BTreeSet<String>> = None;
    let mut ref_counts: Option<(usize, usize)> = None;

    for perm in permutations(n) {
        let col = ExecutionCollector::new();
        explore(
            || prog.clone(),
            &col,
            Config::default().with_priorities(perm.clone()),
        );

        has_bottom_read |= any_bottom_read(&col);

        let full_keys: BTreeSet<String> = col.full_keys().into_iter().collect();
        let terminal = col.terminal_keys();
        let terminal_set: BTreeSet<String> = terminal.iter().cloned().collect();

        // (1)+(2) both full and full union blocked match the brute-force reference.
        if let Some((bf_full, bf_term)) = &reference {
            assert_eq!(
                &full_keys, bf_full,
                "case {case} perm {perm:?}: full executions disagree with brute force\n\
                 program: {:#?}",
                prog.threads
            );
            assert_eq!(
                &terminal_set, bf_term,
                "case {case} perm {perm:?}: terminal (full∪blocked) set disagrees with brute force\n\
                 program: {:#?}",
                prog.threads
            );
        }

        // (3) no duplicate terminal executions.
        assert_eq!(
            terminal.len(),
            terminal_set.len(),
            "case {case} perm {perm:?}: duplicate terminal graphs\nprogram: {:#?}",
            prog.threads
        );

        // (4) terminal set and counts invariant to the priority permutation.
        match (&ref_terminal, &ref_counts) {
            (None, _) => {
                ref_terminal = Some(terminal_set);
                ref_counts = Some((col.full_count(), col.blocked_count()));
            }
            (Some(rt), Some(rc)) => {
                assert_eq!(
                    &terminal_set, rt,
                    "case {case} perm {perm:?}: terminal key set differs between permutations\n\
                     program: {:#?}",
                    prog.threads
                );
                assert_eq!(
                    (col.full_count(), col.blocked_count()),
                    *rc,
                    "case {case} perm {perm:?}: counts differ between permutations\n\
                     program: {:#?}",
                    prog.threads
                );
            }
            _ => unreachable!(),
        }
    }

    let (full, blocked) = ref_counts.expect("at least one permutation");
    ProgCheck {
        full,
        blocked,
        brute_forced: reference.is_some(),
        has_bottom_read,
    }
}

/// Number of non-blocking receives (`recv_timeout`) in `prog`, across all threads.
fn count_nb_receives(prog: &SeqProgram) -> usize {
    prog.threads
        .iter()
        .flatten()
        .filter(|l| {
            matches!(
                l,
                Label::Recv {
                    blocking: false,
                    ..
                }
            )
        })
        .count()
}

/// Number of nondet events in `prog`, across all threads.
fn count_nondets(prog: &SeqProgram) -> usize {
    prog.threads
        .iter()
        .flatten()
        .filter(|l| matches!(l, Label::Nondet { .. }))
        .count()
}

/// Aggregate statistics of a corpus run.
struct CorpusStats {
    progs: usize,
    total_full: usize,
    total_blocked: usize,
    brute_forced: usize,
    with_blocked: usize,
    /// Programs with at least one nothing-reading terminal execution (non-blocking timeouts).
    with_bottom_read: usize,
    /// Programs with >= 2 non-blocking receives - the structural precondition for two
    /// concurrent nothing-readers. Guards the generator against degenerating so the
    /// differential fuzz keeps exercising multi-reader nothing.
    with_multi_nb: usize,
    /// Programs with at least one nondet event. Guards the generator so the differential
    /// fuzz keeps cross-checking the nondet enumeration.
    with_nondet: usize,
}

/// Run `n_progs` random programs from `seed`.
fn run_corpus(seed: u64, n_progs: usize) -> CorpusStats {
    let mut rng = Rng::new(seed);
    let mut stats = CorpusStats {
        progs: n_progs,
        total_full: 0,
        total_blocked: 0,
        brute_forced: 0,
        with_blocked: 0,
        with_bottom_read: 0,
        with_multi_nb: 0,
        with_nondet: 0,
    };
    for case in 0..n_progs {
        let prog = gen_program(&mut rng);
        if count_nb_receives(&prog) >= 2 {
            stats.with_multi_nb += 1;
        }
        if count_nondets(&prog) >= 1 {
            stats.with_nondet += 1;
        }
        let c = check_program(case, &prog);
        stats.total_full += c.full;
        stats.total_blocked += c.blocked;
        if c.brute_forced {
            stats.brute_forced += 1;
        }
        if c.blocked > 0 {
            stats.with_blocked += 1;
        }
        if c.has_bottom_read {
            stats.with_bottom_read += 1;
        }
    }
    stats
}

/// Fast corpus for `cargo test`. Deterministic seed; ~250 programs, ~1s debug.
#[test]
fn fuzz_small_corpus() {
    let s = run_corpus(0x5EED_1234, 250);
    assert_eq!(s.progs, 250);
    // The corpus is non-degenerate: it exercises full executions, blocked executions,
    // and most programs are fully cross-checked (full union blocked) against brute force.
    assert!(s.total_full > 0, "corpus produced no full executions");
    assert!(
        s.total_blocked > 0,
        "corpus produced no blocked executions — the full∪blocked check is exercised nowhere"
    );
    assert!(
        s.with_blocked >= 20,
        "too few programs with a blocked terminal ({}/250)",
        s.with_blocked
    );
    // Non-blocking receives are genuinely exercised: some programs have a nothing-reading
    // (timeout) terminal execution, cross-checked against the brute-force reference.
    assert!(
        s.with_bottom_read >= 20,
        "too few programs with a ⊥-reading terminal ({}/250) — non-blocking receives \
         barely exercised",
        s.with_bottom_read
    );
    // Multi-reader nothing is genuinely exercised: >= 2 non-blocking receives - the
    // structural precondition for two concurrent nothing-readers - appears in enough programs.
    // Actual for this seed is 40/250; the threshold keeps a wide margin so a future
    // generator tweak that quietly stops emitting multiple nb receives fails here.
    assert!(
        s.with_multi_nb >= 25,
        "too few programs with ≥ 2 non-blocking receives ({}/250) — multi-reader ⊥ \
         barely exercised; the generator may have degenerated",
        s.with_multi_nb
    );
    // Nondet is genuinely exercised: enough programs contain a nondet event, so the brute
    // force keeps cross-checking the nondet enumeration and its canonicity.
    assert!(
        s.with_nondet >= 20,
        "too few programs with a nondet event ({}/250) — data-nondeterminism barely \
         exercised; the generator may have degenerated",
        s.with_nondet
    );
    assert!(
        s.brute_forced * 5 >= s.progs * 4,
        "too many programs exceeded the brute-force budget ({}/{}); generation too large",
        s.brute_forced,
        s.progs
    );
}

/// Larger corpus (a few seconds), run only in release builds. Different seed for extra
/// coverage.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: 800-program fuzz corpus; run with --release"
)]
fn fuzz_large_corpus() {
    let s = run_corpus(0xA11C_E777, 800);
    assert_eq!(s.progs, 800);
    assert!(s.total_full > 0);
    assert!(s.total_blocked > 0);
}
