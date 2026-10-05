//! **The mode ladder** (`C1_HARDENING_SPEC` §D.4, step 6 of §E.2): a diagnostic that localises
//! any completeness loss of T2 to a *single* mechanism, by switching the pruners on one at a
//! time and diffing the realizable terminal sets of adjacent rungs.
//!
//! | level | T-DES | T-CANON + PASS oracle | T-PRED (line 7) | T-GATE (lines 9/13) | role |
//! |---|---|---|---|---|---|
//! | L1 | ✓ | — (untimed canon) | — | — | `with_time_zombie()` — correct by construction |
//! | L2 | ✓ | ✓ | — | — | isolates the canon (γ2/γ3/γ4/R1) |
//! | L3 | ✓ | ✓ | ✓ | — | isolates T-PRED |
//! | L4 | ✓ | ✓ | ✓ | ✓ | `with_time_predicate()` — the shipping regime |
//! | **L2′** | ✓ | **arms 18/19/22 ≡ true** | ✓ | ✓ | Т-RED′'s `T2⁰` — isolates *pruning* from *canon* |
//!
//! `L2′` is not a rung of the same monotone scale: it is L4 with **all three** canon arms disabled
//! (`Config::with_canon_free()`). Т-RED′ (`T2_COMPLETENESS_VI_2` §0.1) proves its tree is zombie's
//! plus revisits minus exactly what T-PRED/T-GATE cut, so `realizable(L4) ⊆ realizable(L2′) ⊆
//! realizable(L1)` — and a strict inclusion on either side names the culprit of a loss (left ⇒ the
//! canon, right ⇒ global C1). Both are asserted per program by [`ladder_check`].
//!
//! Arm **18** belongs in that list, and the original Т-RED (over {19, 22} only) is refuted for
//! omitting it: since `pass_nb` made the non-blocking canon existential rather than the structural
//! "reads ⊥", an active arm 18 can reject a revisit zombie performs, so T2⁰ would stop majorising
//! the zombie tree. Measured here: forcing arm 18 changes `L2′` on the corpora that actually have
//! a non-⊥ non-blocking receive in `Deleted` (timed 3000: 24 809 → 26 961 Visits, 99 → 860
//! duplicates; value-dependent 2000: 115 969 Visits, 1796 duplicates) and leaves the rest
//! untouched — while every inclusion still holds.
//!
//! L1 is *not* a re-implementation: `Config::with_time_predicate_level(1)` delegates to the
//! existing zombie regime, which is the untimed Algorithm 1 (Theorem 4.1 verbatim) under the DES
//! insertion order plus the proven post-hoc terminal filter, and which is already validated
//! bit-for-bit against T1 on the 820-program corpus and on raft. On L1–L3 the terminals are
//! routed through that same post-filter (without T-PRED/T-GATE the walk *does* reach graphs no
//! schedule realizes), so "realizable keys" means the same object on every rung.
//!
//! # What an assertion here means
//!
//! `realizable(L1) == realizable(L2) == realizable(L3) == realizable(L4)` **as key sets** is a
//! genuine certificate *for the programs in the corpus* (L1 is correct by construction), and each
//! adjacent pair pins the blame: `L1 != L2` ⇒ the canon; `L2 != L3` ⇒ T-PRED; `L3 != L4` ⇒ the
//! forced-closure gate. What it does **not** certify: anything outside the corpus, and anything
//! about optimality-(b) — hence the dead-branch counts, which are recorded as *facts* (see
//! [`DeadFacts`]), never asserted.
//!
//! A red assertion in this file is a **finding**, not a test to be fixed: minimise the program,
//! pin it as an `#[ignore]` witness, and report the mechanism.
//!
//! # The one anomaly the ladder found — and why it is not a T2 bug
//!
//! No rung ever lost or invented a realizable terminal. What the hybrid rungs *do* produce is
//! **duplicates**, on two independent shapes:
//!
//! * `ladder_r1_l2_duplicate_witness`: L2 records 4 terminals for 3 distinct keys;
//! * `ladder_self_witness_probe`: the debug-only §0.7 self-witness assertion fires at **L2 only**
//!   (cases 333, 394 of the 2000-program value-dependent corpus; never at L1/L3/**L4**).
//!
//! Both are one mechanism. L2/L3 run the T2 canon *without* the pruners it presumes, so the PASS
//! oracle is asked about graphs the shipping regime never reaches; on those, `viable` answers
//! "false" for every competitor, `V = ∅`, and PASS — antitone in `V` — makes **every** reaching
//! holder canonical instead of exactly one. That is the safe direction (M1, §0.1): a duplicate,
//! never a loss. It says nothing against L4, where the same graphs are pruned before the canon
//! sees them; if anything the probe *strengthens* the §0.7 evidence, extending "no self-witness
//! failure on the shipping regime" from 400 to 2000 value-dependent programs, and now to 400
//! canon-directed ones as well.
//!
//! The same measurement is what scoped the §0.7 assertion itself: it fired on **36 of 400**
//! directed programs and **2 of 2000** value-dependent ones, in both cases *only* at L2, never at
//! L1/L3/L4/L2′. Since B1.a is proved only under premise (H) = "the line-9 gate passed", and L2
//! switches that gate off, the assertion was out of contract there; it is now guarded by
//! `time_level >= 4` (`revisit.rs::assert_self_witness`), which leaves the shipping regime checked
//! exactly as before. Drop that guard to re-measure.
//!
//! # Corpora
//!
//! * (а) the value-**independent** timed `SeqProgram` generator of `tests/fuzz_timed.rs`;
//! * (б) the value-**dependent** generator of `tests/fuzz_value_dependent.rs` — the important
//!   one: value independence is exactly what hid the historical raft f1 28-vs-40 loss, and what
//!   made the 820-corpus blind to R1;
//! * (в1) the **directed canon corpus** ([`canon_corpus`]) — built specifically because (а) and (б)
//!   leave the `L1 ↔ L2` rung vacuous; reject-sampled on the divergence detector, it hits the
//!   shape on ~80 % of candidates (300/369 and 3000/3736);
//! * (в2) two pinned shapes: the 6-thread L3 counterexample (`TIME_PLAN`, "Контрпример") and the
//!   R1 witness of `tests/r1_line22.rs`.
//!
//! The two random generators are **verbatim copies** of the originals (same `Rng`, same seeds ⇒ the
//! same programs), deliberately duplicated rather than shared: the ladder must keep working even if
//! a generator is later retuned, and `tests/fuzz_*.rs` own their corpora. (The only edits to the
//! copies are visibility: `pub` on the program structs and on `Op`/`Sel`, so the module handles can
//! return them and the directed generator can build on the same interpreter — one interpreter means
//! one `possible_future`, and no second chance to introduce an unsound one.)
//!
//! # Measured, July 2026 — the ladder is green everywhere, and *why* each rung prunes
//!
//! Corpora (**every** rung, `L2′` included, agrees on the realizable key set on every program):
//!
//! | corpus | progs | walk differs L1/L2 | L2/L3 | L3/L4 |
//! |---|---|---|---|---|
//! | timed (а) | 250 + 3000 | 0, 2 | 13, 198 | 0, 6 |
//! | value-dependent (б) | 150 + 2000 | 0, 3 | 40, 497 | 16, 234 |
//! | **canon-directed (в1)** | **300 + 3000** | **300, 3000** | 300, 3000 | 79, 729 |
//!
//! Where "walk differs" is 0 the corresponding equality is **vacuous** — the two rungs ran the same
//! search. That was the whole motivation for corpus (в1): on random programs the canon rung is
//! essentially never exercised (0/250, 0/150, 2/3000, 3/2000 even after the detector was sharpened
//! to compare *which branch each revisit fired from*, which is the canon's only job), so the
//! `L1 == L2` equality there proves next to nothing. On the directed corpus it is exercised by
//! construction, 3000/3000, and still holds.
//!
//! `examples/raft_election_timed --level {1,2,3,4} [--canon-free]` (12 threads; "recorded →
//! distinct" = terminals recorded → distinct `canonical_key`s, via `--dump-keys`):
//!
//! | run | L1 (zombie) | L2 | L3 | L4 | L2′ |
//! |---|---|---|---|---|---|
//! | `--faults 0` | 8 (62.8 s) | 8 | 8 | 8 (6.6 ms) | 8 |
//! | `--faults 1` | 40 (109 s) | 40 | 40 | 40 (12 ms) | 46 recorded → **40** distinct |
//! | `--bug --timeouts 100,105,200` | 820 (412 s) | 820 | 820 | 820 (0.15 s) | 2967 recorded → **820** distinct |
//!
//! Compared **as key sets** (`--dump-keys` diff, not merely counts) on `--faults 0`, `--faults 1`
//! and `--bug`: L1 = L2 = L3 = L4 = L2′, exactly. `L2′`'s extra *records* are duplicates to the
//! last one (6 on f1, 2147 on `--bug`) — which is the measured price of forcing arms 19/22 and
//! precisely what Т-RED predicts, since it is stated over sets.
//!
//! `--bug` reports 712 full + 108 error terminals on **every** rung: the `--bug = 108` oracle now
//! holds at L1, where it is a *theorem* (Theorem 4.1 + the proven terminal filter), and not only
//! under T2 — a strictly stronger statement of that oracle than before the ladder existed.
//!
//! Two facts worth keeping:
//! * on raft the **canon alone** (L2) removes 99.7 % of the untimed superset — not because it
//!   prunes graphs directly, but because `cons_candidates` under the predicate drops
//!   eager-infeasible sources, so a revisit is refused from every branch whose receive holds an
//!   infeasible source and fires only from the canonical (feasible-holder) one. That the
//!   realizable set survives this is exactly the L1-vs-L2 certificate;
//! * `L3 → L4` prunes **nothing** on raft (0/8, 0/40, 0/820 filtered at L3) — the coroutine
//!   runtime's `possible_future` is inexact, so the gate degenerates to raw `check` (Л-G3), which
//!   T-PRED has already applied. The gate earns its keep on `SeqProgram`s (L3 dead 854 → L4 dead
//!   0 on the 2000-program corpus) and on the pinned L3 counterexample (15 Visits → 12).
//!
//! One more measured fact, on the directed corpus: **L4 leaves 729 dead Visit nodes on 729 of the
//! 3000 programs**, although their `possible_future` is exact-shaped (a sound over-approximation,
//! `VdProgram::possible_future`). So "an exact future ⇒ zero dead branches" does not hold in
//! general — matching the prediction in `T2_COMPLETENESS_VI` §8 R-2 that the implicit
//! "`SeqProgram` ⇒ `dead = 0`" is false. This is optimality-(b) only; no terminal is lost.
//!
//! # `pass_nb` (line 18): merged, and structurally invisible to every corpus here
//!
//! The third completeness loss — the non-blocking canon `reads_bottom(ep)`, which tested *local*
//! feasibility where viability was needed — was reproduced and fixed on a parallel track and is
//! merged into this tree (`revisit.rs::pass_nb`, `time::viable_recv_bot`, witness
//! `tests/nb_line18.rs`, pinned at R-1 = 3 and R-2 = 7 realizable keys over all 24 permutations).
//!
//! Re-running every corpus above **before and after** that merge gives *bit-identical* L1/L2/L3/L4
//! statistics — visits, dead, filtered, duplicates, oracle calls, divergence rates, all of them, on
//! 250 + 3000 timed, 150 + 2000 value-dependent and 300 + 3000 canon-directed programs, plus the
//! L3, R1 and canon witnesses. **Zero verdict changes.** The corpora are structurally blind to the
//! shape (they need a non-⊥ non-blocking read in `Deleted` whose ⊥ alternative emits an early
//! competitor), and the directed generator (в1) does not produce it either: its only non-blocking
//! receive is the revisit *victim*, which is never in `Deleted`.
//!
//! Consequences to respect: `tests/nb_line18.rs` is the **only** live coverage of that branch and
//! must stay pinned; a green corpus here is *not* evidence about it. The one place the merge is
//! visible at all is `L2′`, because arm 18 is now forced there too (numbers above).
//!
//! # The ladder as the acceptance gate for any *future* pruner
//!
//! A T-GATE on **line 6** (`visit_nondet`, which has no gate at all) was proposed and **rejected on
//! review**: it prunes before the forced events of the branch exist, so it loses exactly the
//! revisits of the first forced send `w` that line 9 deliberately keeps (A2.1b) — and `r ← w` is
//! the canonical repair of that very infeasibility. It is not in this tree and is not coming.
//!
//! The general point survives the specific proposal: any *fourth* pruner would sit on rung 4, so
//! `realizable(L1) == realizable(L4)` is a direct detector of the completeness it costs, and the
//! canon-directed corpus (в1) is the part likely to exercise it. Re-run everything here —
//! `#[ignore]` corpora included — before accepting one.

mod common;

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

use must::event::{EventId, Label, Val};
use must::graph::ExecutionGraph;
use must::{explore, Config, DeadBranchDetector, ExecutionCollector, Observer, Program};

/// Counts the canon oracle's verdicts, so the report can say whether a rung's *mechanism* was
/// exercised at all. A ladder equality on a corpus where L1 and L2 never diverge proves nothing
/// about the canon, and this is what makes that visible instead of implied.
#[derive(Default)]
struct OracleCounter {
    nondet: AtomicUsize,
    recv: AtomicUsize,
}

impl OracleCounter {
    fn total(&self) -> usize {
        self.nondet.load(Ordering::Relaxed) + self.recv.load(Ordering::Relaxed)
    }
}

/// Records **which graph each backward revisit fired from** — `(source graph key, r, s)`.
///
/// This is the sharp instrument for the canon rung. Arms 19/22 do exactly one thing: decide which
/// of the several branches reaching the same `g2` is allowed to spawn it. A canon change can
/// therefore move a revisit from one branch to another **without moving a single aggregate
/// statistic** (same node count, same terminals, same dead count) — which is precisely what the
/// coarse `(visits, dead, filtered, |keys|)` proxy misses. Comparing these sets across rungs
/// measures the mechanism itself.
#[derive(Default)]
struct RevisitRecorder {
    fired: Mutex<BTreeSet<String>>,
}

impl RevisitRecorder {
    fn set(&self) -> BTreeSet<String> {
        self.fired.lock().unwrap().clone()
    }
}

impl Observer for RevisitRecorder {
    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        _deleted: &BTreeSet<EventId>,
    ) {
        self.fired
            .lock()
            .unwrap()
            .insert(format!("{r}<-{s} from {}", g.canonical_key()));
    }
}

impl Observer for OracleCounter {
    fn on_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _v: Val,
        _revisiting: EventId,
        _rev_label: &Label,
        _verdict: bool,
    ) {
        self.nondet.fetch_add(1, Ordering::Relaxed);
    }
    fn on_viable_recv_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _src: EventId,
        _revisiting: EventId,
        _rev_label: &Label,
        _verdict: bool,
    ) {
        self.recv.fetch_add(1, Ordering::Relaxed);
    }
}

/// SplitMix64 — reproducible with no external crate (copy of `fuzz.rs`, shared by both
/// generators below so the corpora reproduce their originals exactly).
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
    fn chance(&mut self, pct: usize) -> bool {
        self.below(100) < pct
    }
}

// == The ladder runner =======================================================================

/// The four rungs, in order.
const LEVELS: [u8; 4] = [1, 2, 3, 4];

/// One rung's observable output.
#[derive(Debug, Clone)]
struct LevelRun {
    /// Canonical keys of every *recorded* terminal (full + blocked + error) — i.e. the
    /// eager-realizable ones, on every rung (L1–L3 post-filter, L4 by construction).
    realizable: BTreeSet<String>,
    /// The same keys as a multiset, for the no-duplicate check (optimality-(a)).
    realizable_len: usize,
    /// `realizable_len - |realizable|`: how many terminals this rung recorded twice.
    ///
    /// **Zero is a theorem only on L1 and L4** (see [`ladder_check`]); on the hybrid rungs it is
    /// a measured fact, and on `L2′` duplicates are the *point* (arms 19/22 ≡ true). L2/L3 run the
    /// T2 canon while *not* running the pruners the canon presumes, so the PASS oracle is
    /// evaluated on graphs the shipping regime never reaches. PASS is antitone in the viable set
    /// `V`, and by `T2_GAMMA_FRONTIER` §Ⅰ (lemma LEX) / §Ⅳ the number of holders that pass is
    /// exactly `|{v ∈ R : v ≤ min(V)}|` — a *continuous* cost of narrowing `V`, of which `V = ∅`
    /// (every reaching holder passes) is only the limiting case. (`C1_HARDENING_SPEC` §0.7 stated
    /// this as a discontinuity; that formulation is refuted, but the direction — duplicate, never
    /// loss — is unchanged.)
    dups: usize,
    /// Terminals the post-filter suppressed (always empty on L4).
    filtered: usize,
    /// Visit nodes whose subtree bore no *recorded* terminal (optimality-(b) — a fact, not a
    /// requirement: on L1–L3 a branch producing only filtered terminals counts as dead, which is
    /// exactly the quantity the T2 gate exists to remove).
    dead: usize,
    /// Total Visit nodes entered.
    visits: usize,
    /// `viable` + `viable_recv` verdicts computed (0 on L1, which has no oracle).
    oracle_calls: usize,
    /// The `(source graph, r, s)` of every backward revisit taken — see [`RevisitRecorder`].
    revisits: BTreeSet<String>,
}

/// Run `make`'s program at ladder level `level` (sequentially — `DeadBranchDetector` is only
/// meaningful on one thread).
fn run_level<P, MK>(make: MK, level: u8) -> LevelRun
where
    MK: Fn() -> P + Sync,
    P: Program,
{
    run_cfg(
        make,
        Config::default()
            .collect_errors()
            .with_time_predicate_level(level),
    )
}

/// The **`L2′` rung** = Т-RED's `T2⁰` (`T2_COMPLETENESS_VI` §3.1, recipe §8 R-7): the full
/// predicate (level 4 — T-DES, T-PRED, both T-GATEs) with the two canon arms 19/22 forced to
/// `true`. Its role is a two-way inclusion, not an equality; see [`ladder_check`].
fn run_l2_prime<P, MK>(make: MK) -> LevelRun
where
    MK: Fn() -> P + Sync,
    P: Program,
{
    run_cfg(
        make,
        Config::default()
            .collect_errors()
            .with_time_predicate_level(4)
            .with_canon_free(),
    )
}

/// One `explore` under an arbitrary ladder config, reduced to a [`LevelRun`].
fn run_cfg<P, MK>(make: MK, cfg: Config) -> LevelRun
where
    MK: Fn() -> P + Sync,
    P: Program,
{
    let obs = (
        ExecutionCollector::new(),
        (
            DeadBranchDetector::new(),
            (OracleCounter::default(), RevisitRecorder::default()),
        ),
    );
    explore(make, &obs, cfg);
    let (col, (dead, (oracle, revisits))) = &obs;
    let mut keys = col.terminal_keys();
    keys.extend(col.error_keys());
    let realizable: BTreeSet<String> = keys.iter().cloned().collect();
    LevelRun {
        realizable_len: keys.len(),
        dups: keys.len() - realizable.len(),
        realizable,
        filtered: col.filtered_count(),
        dead: dead.dead(),
        visits: dead.visits(),
        oracle_calls: oracle.total(),
        revisits: revisits.set(),
    }
}

/// The five rungs a program is run at, in the order [`ladder_check`] returns them.
const RUNGS: [&str; 5] = ["1", "2", "3", "4", "2'"];

/// Accumulated dead-branch / visit facts over a corpus, per rung (index 4 = `L2′`).
#[derive(Default, Debug)]
struct DeadFacts {
    dead: [usize; 5],
    visits: [usize; 5],
    filtered: [usize; 5],
    /// Programs on which this level reported ≥ 1 dead Visit.
    progs_with_dead: [usize; 5],
    /// Duplicate realizable keys (fact on L2/L3, theorem `= 0` on L1/L4, expected on `L2′`).
    dups: [usize; 5],
    /// Programs on which this level recorded ≥ 1 duplicate.
    progs_with_dups: [usize; 5],
    /// Canon-oracle verdicts computed on this level.
    oracle_calls: [usize; 5],
    /// **Ladder sensitivity**: programs whose *walk* (Visit count) differs from the previous
    /// rung's. `sensitivity[i]` compares `L(i+1)` with `L(i)`, so index 0 is L1-vs-L2 (the canon),
    /// 1 is L2-vs-L3 (T-PRED), 2 is L3-vs-L4 (T-GATE). Where this is 0 the corresponding equality
    /// of realizable sets is *vacuous* — the two rungs ran the same search — and must not be read
    /// as evidence about that mechanism.
    sensitivity: [usize; 3],
    /// Programs measured.
    progs: usize,
}

impl DeadFacts {
    /// Accumulate one program's five runs (L1..L4 then `L2′`).
    fn add_program(&mut self, runs: &[LevelRun]) {
        self.progs += 1;
        for (i, run) in runs.iter().enumerate() {
            self.dead[i] += run.dead;
            self.visits[i] += run.visits;
            self.filtered[i] += run.filtered;
            self.dups[i] += run.dups;
            self.oracle_calls[i] += run.oracle_calls;
            if run.dead > 0 {
                self.progs_with_dead[i] += 1;
            }
            if run.dups > 0 {
                self.progs_with_dups[i] += 1;
            }
        }
        for i in 0..LEVELS.len() - 1 {
            // "The walk differed" = any of the shape statistics moved. Visit *count* alone is too
            // coarse: two rungs can enter the same number of nodes yet build different trees
            // (measured: the 3000-program timed corpus, where L1 and L2 both enter 25195 nodes but
            // 4 of them are dead only under L2).
            let (a, b) = (&runs[i], &runs[i + 1]);
            if (a.visits, a.dead, a.filtered, a.realizable_len)
                != (b.visits, b.dead, b.filtered, b.realizable_len)
                || a.revisits != b.revisits
            {
                self.sensitivity[i] += 1;
            }
        }
    }
    fn report(&self, name: &str) {
        println!("== ladder facts [{name}] ({} programs) ==", self.progs);
        for (i, l) in RUNGS.iter().enumerate() {
            println!(
                "   L{l}: visits={} dead={} ({} progs) filtered_terminals={} dups={} ({} progs) \
                 oracle_calls={}",
                self.visits[i],
                self.dead[i],
                self.progs_with_dead[i],
                self.filtered[i],
                self.dups[i],
                self.progs_with_dups[i],
                self.oracle_calls[i]
            );
        }
        println!(
            "   walk differs: L1!=L2 on {}/{} progs, L2!=L3 on {}/{}, L3!=L4 on {}/{}",
            self.sensitivity[0],
            self.progs,
            self.sensitivity[1],
            self.progs,
            self.sensitivity[2],
            self.progs
        );
    }
}

/// Run all four rungs on one program and assert the ladder invariants:
///   1. `realizable(L1) == realizable(L2) == realizable(L3) == realizable(L4)` — the headline
///      certificate; the adjacent diff is reported first, so a failure names the guilty mechanism;
///   2. no duplicate realizable key **on L1 and L4** (optimality-(a)).
///
/// # Why the no-duplicate check is asserted on L1/L4 only
///
/// Both are *coherent* regimes: L1 is the untimed Algorithm 1 (Theorem 4.1 verbatim) under the DES
/// policy with a post-hoc filter — a subset of a duplicate-free set is duplicate-free — and L4 is
/// the shipping T2, whose no-dup the existing corpora already assert.
///
/// L2 and L3 are deliberately *incoherent*: they run the T2 canon while withholding the pruners
/// that canon presumes, so the PASS oracle gets evaluated on graphs the shipping regime never
/// reaches. PASS is antitone in the viable set `V`, and the number of holders that pass is exactly
/// `|{v ∈ R : v ≤ min(V)}|` (`T2_GAMMA_FRONTIER` §Ⅰ/§Ⅳ), so narrowing `V` costs duplicates
/// continuously, with `V = ∅` — every reaching holder passes — as the limiting case. That is the
/// *safe* direction (a duplicate, never a loss — M1, `C1_HARDENING_SPEC` §0.1), and it is exactly
/// why the ladder's headline invariant is stated over key **sets**. Duplicates on L2/L3 are
/// therefore recorded as a measured fact, not asserted away. (Measured: the R1 witness produces one
/// such duplicate on L2 — see `ladder_r1_witness`.)
///
/// # The `L2′` rung: Т-RED's two-way inclusion (`T2_COMPLETENESS_VI` §3.1, §8 R-7)
///
/// `L2′` is L4 with arms 19/22 ≡ `true`. Т-RED proves its tree is zombie's plus revisits minus
/// exactly what T-PRED/T-GATE cut, so
///
/// ```text
/// realizable(L4) ⊆ realizable(L2′) ⊆ realizable(L1 = zombie)
/// ```
///
/// must hold, and each strict inclusion *names the culprit of a loss*: `L4 ⊊ L2′` ⇒ the canon
/// (arms 19/22) dropped a terminal; `L2′ ⊊ L1` ⇒ a pruner did (global C1). This is the cheapest
/// machine disjunction between the two open questions (Q1)/(Q2) of §3.1 — and, because Т-RED is a
/// *proved* lemma, a violation of either inclusion refutes the lemma and must be reported, not
/// patched.
///
/// Returns the four rungs (index 0..3) followed by `L2′` (index 4), so the caller can accumulate
/// the facts.
fn ladder_check<P, MK>(ctx: &str, make: MK) -> Vec<LevelRun>
where
    MK: Fn() -> P + Sync + Copy,
    P: Program,
{
    let mut runs: Vec<LevelRun> = LEVELS.iter().map(|&l| run_level(make, l)).collect();
    let l2p = run_l2_prime(make);

    // Т-RED, left inclusion: arms ≡ true is weaker than the canon ⇒ L4's tree ⊆ L2′'s.
    assert!(
        runs[3].realizable.is_subset(&l2p.realizable),
        "{ctx}: T-RED VIOLATED — realizable(L4) ⊄ realizable(L2′); the canon arms cannot *add* \
         terminals.\n  missing from L2′ ({}): {:#?}",
        runs[3].realizable.difference(&l2p.realizable).count(),
        runs[3]
            .realizable
            .difference(&l2p.realizable)
            .collect::<Vec<_>>()
    );
    // Т-RED, right inclusion: zombie is complete, so no regime may invent a terminal.
    assert!(
        l2p.realizable.is_subset(&runs[0].realizable),
        "{ctx}: T-RED VIOLATED — realizable(L2′) ⊄ realizable(zombie); L2′ invented a terminal \
         zombie (correct by construction) never found.\n  extra in L2′ ({}): {:#?}",
        l2p.realizable.difference(&runs[0].realizable).count(),
        l2p.realizable
            .difference(&runs[0].realizable)
            .collect::<Vec<_>>()
    );
    runs.push(l2p);

    for i in [0, LEVELS.len() - 1] {
        assert_eq!(
            runs[i].dups,
            0,
            "{ctx}: L{} produced {} duplicate realizable terminal(s) (optimality-(a); \
             |keys| = {}, |set| = {})",
            LEVELS[i],
            runs[i].dups,
            runs[i].realizable_len,
            runs[i].realizable.len()
        );
    }
    for i in 0..LEVELS.len() - 1 {
        let (a, b) = (&runs[i], &runs[i + 1]);
        let (la, lb) = (LEVELS[i], LEVELS[i + 1]);
        if a.realizable != b.realizable {
            let lost: Vec<&String> = a.realizable.difference(&b.realizable).collect();
            let extra: Vec<&String> = b.realizable.difference(&a.realizable).collect();
            panic!(
                "{ctx}: LADDER DIFF L{la} != L{lb} — the mechanism switched on at L{lb} is \
                 responsible.\n  |L{la}| = {}, |L{lb}| = {}\n  lost by L{lb} ({}): {:#?}\n  \
                 extra in L{lb} ({}): {:#?}",
                a.realizable.len(),
                b.realizable.len(),
                lost.len(),
                lost,
                extra.len(),
                extra
            );
        }
    }
    runs
}

// == Corpus (а): the value-independent timed `SeqProgram` generator ==========================

/// Verbatim copy of `tests/fuzz_timed.rs`'s generator (same `Rng`, same seeds ⇒ literally the
/// same programs), plus the pinned 6-thread L3 counterexample from `tests/forced_closure.rs`.
mod timed_corpus {
    use super::Rng;
    use crate::common::{recv, recv_eq, SeqProgram};
    use must::event::{Label, Model, Pred, Window};

    /// A send with a finite delivery window `[lo, hi]` (copy of `tests/forced_closure.rs`).
    fn tsend(dst: usize, v: &str, lo: u64, hi: u64) -> Label {
        Label::send_within(Model::Asyn, dst, v, Window::new(lo, hi))
    }

    /// The 6-thread L3 program (`TIME_PLAN` "Контрпример", copy of `tests/forced_closure.rs`):
    /// ```text
    /// T0: r  = recv(any)
    /// T1: a  = send(T0,"a",[1,100])
    /// T2: rg = recv(=g);  m = send(T0,"b0",[0,0])
    /// T3: g  = send(T2,"g",[5,5])
    /// T4: rs = recv(=x);  s = send(T0,"b", [0,0])
    /// T5: x  = send(T4,"x",[30,30])
    /// ```
    pub fn l3_program() -> SeqProgram {
        SeqProgram::new(vec![
            vec![recv()],                             // T0
            vec![tsend(0, "a", 1, 100)],              // T1
            vec![recv_eq("g"), tsend(0, "b0", 0, 0)], // T2
            vec![tsend(2, "g", 5, 5)],                // T3
            vec![recv_eq("x"), tsend(0, "b", 0, 0)],  // T4
            vec![tsend(4, "x", 30, 30)],              // T5
        ])
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

    /// Public handle for the (private, verbatim-copied) generator above.
    pub fn gen(rng: &mut Rng) -> SeqProgram {
        gen_program(rng)
    }
}

// == Corpus (б): the value-dependent generator ===============================================

/// Verbatim copy of `tests/fuzz_value_dependent.rs`'s program table and generator (same `Rng`,
/// same seeds ⇒ literally the same programs).
mod vd_corpus {
    use super::Rng;
    use must::event::{Label, Model, Pred, Window};
    use must::intern::resolve;
    use must::{Program, ThreadNext, Val};

// -- The value-dependent program table ------------------------------------------------------

/// A receive's selectivity: static, or keyed by the value an earlier op of the SAME thread
/// produced (a nondet choice or a receive's read — the (а) axis).
#[derive(Clone, Copy, Debug)]
pub enum Sel {
    Any,
    Eq(&'static str),
    /// `Pred::eq(value_of(op[k]))`; a guard with no value (⊥ read) yields a never-matching
    /// predicate.
    EqGuard(usize),
}

/// One straight-line op of a thread. Guards always reference a po-earlier, value-producing
/// op (Nondet / Recv) of the same thread.
#[derive(Clone, Debug)]
pub enum Op {
    /// `nd{a, b}`.
    Nondet,
    Send {
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    /// Emitted only when `value_of(op[guard]) == eq` — the (б) emit/no-emit axis.
    SendIf {
        guard: usize,
        eq: &'static str,
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    /// Window `[lo1,hi1]` when `value_of(op[guard]) == eq`, else `[lo2,hi2]` — the (в) axis.
    SendWin {
        guard: usize,
        eq: &'static str,
        dst: usize,
        model: Model,
        val: &'static str,
        lo1: u64,
        hi1: u64,
        lo2: u64,
        hi2: u64,
    },
    Recv {
        sel: Sel,
        blocking: bool,
    },
}

impl Op {
    fn is_value_producing(&self) -> bool {
        matches!(self, Op::Nondet | Op::Recv { .. })
    }
}

/// The interpretable program: `threads[t]` is thread `t`'s op list.
#[derive(Clone, Debug)]
pub struct VdProgram {
    pub threads: Vec<Vec<Op>>,
}

/// Value of guard op `k` given the resolved `vals`, when it equals `eq`.
fn guard_hits(vals: &[Option<Val>], k: usize, eq: &str) -> bool {
    vals[k].is_some_and(|v| resolve(v) == eq)
}

/// The label op `op` produces given the thread's resolved `vals` so far.
fn op_label(op: &Op, vals: &[Option<Val>]) -> Label {
    match op {
        Op::Nondet => Label::nondet(["a", "b"]),
        Op::Send {
            dst,
            model,
            val,
            lo,
            hi,
        } => Label::send_within(*model, *dst, *val, Window::new(*lo, *hi)),
        Op::SendIf {
            dst,
            model,
            val,
            lo,
            hi,
            ..
        } => Label::send_within(*model, *dst, *val, Window::new(*lo, *hi)),
        Op::SendWin {
            guard,
            eq,
            dst,
            model,
            val,
            lo1,
            hi1,
            lo2,
            hi2,
        } => {
            let (lo, hi) = if guard_hits(vals, *guard, eq) {
                (*lo1, *hi1)
            } else {
                (*lo2, *hi2)
            };
            Label::send_within(*model, *dst, *val, Window::new(lo, hi))
        }
        Op::Recv { sel, blocking } => {
            let pred = match sel {
                Sel::Any => Pred::any(),
                Sel::Eq(s) => Pred::eq(*s),
                Sel::EqGuard(k) => match vals[*k] {
                    Some(v) => Pred::eq(resolve(v)),
                    None => Pred::eq("__none__"), // never matches the {a,b} payloads
                },
            };
            if *blocking {
                Label::recv(pred)
            } else {
                Label::recv_nb(pred)
            }
        }
    }
}

/// Replay one thread against its trace: resolved per-op values, plus the index of the first
/// op not yet committed (skipped `SendIf`s never consume a trace entry).
fn replay(ops: &[Op], trace: &[Option<Val>]) -> (Vec<Option<Val>>, usize) {
    let mut vals: Vec<Option<Val>> = vec![None; ops.len()];
    let mut cursor = 0;
    for (i, op) in ops.iter().enumerate() {
        let emits = match op {
            Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
            _ => true,
        };
        if !emits {
            continue; // no event, no trace entry
        }
        if cursor < trace.len() {
            if op.is_value_producing() {
                vals[i] = trace[cursor];
            }
            cursor += 1;
        } else {
            return (vals, i);
        }
    }
    (vals, ops.len())
}

impl Program for VdProgram {
    fn num_threads(&self) -> usize {
        self.threads.len()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        self.threads
            .iter()
            .enumerate()
            .map(|(t, ops)| {
                let (vals, frontier) = replay(ops, &traces[t]);
                // The frontier op may itself be a skipped SendIf whose guard resolves only
                // later — replay already skipped those; find the first op at/after `frontier`
                // that emits under the resolved vals.
                let mut i = frontier;
                while i < ops.len() {
                    let emits = match &ops[i] {
                        Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
                        _ => true,
                    };
                    if emits {
                        return ThreadNext::Next(op_label(&ops[i], &vals));
                    }
                    i += 1;
                }
                ThreadNext::Finished
            })
            .collect()
    }
    /// Sound over-approximation: for every op at/after the frontier, include every label it
    /// could produce under ANY assignment of still-unresolved guards. A guard already
    /// resolved narrows the set; an unresolved (or ⊥-valued) one contributes all variants.
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        let ops = &self.threads[tid];
        let (vals, frontier) = replay(ops, trace);
        // Contract (`src/program.rs`): `out[0]` must be *exactly* the thread's next label - the
        // one `next` reports, i.e. `op_label` of the first **emitting** op at/after the frontier
        // (a `SendIf` with a failing guard is skipped by both). Everything from index 1 on
        // over-approximates the ops strictly after it.
        //
        // The head cannot come from the loop below: that loop deliberately emits *several*
        // labels for one op (both windows of an unresolved `SendWin`), so it would put the wrong
        // label at index 0. `force_source` condition (3b) does `.skip(1)` on the strength of
        // this, so a mismatch is an over-force - a completeness loss, not a crash.
        let Some(head) = (frontier..ops.len()).find(|&i| match &ops[i] {
            Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
            _ => true,
        }) else {
            return Some(Vec::new()); // finished: no future events at all (the exact answer)
        };
        let mut out = vec![op_label(&ops[head], &vals)];
        for op in &ops[head + 1..] {
            match op {
                Op::Nondet => out.push(op_label(op, &vals)),
                Op::Send { .. } => out.push(op_label(op, &vals)),
                Op::SendIf { guard, eq, .. } => match vals[*guard] {
                    Some(v) if resolve(v) != *eq => {} // definitely skipped
                    _ => out.push(op_label(op, &vals)), // may emit
                },
                Op::SendWin {
                    guard,
                    dst,
                    model,
                    val,
                    lo1,
                    hi1,
                    lo2,
                    hi2,
                    ..
                } => match vals[*guard] {
                    Some(_) => out.push(op_label(op, &vals)),
                    None => {
                        // Unresolved guard: both windows are possible.
                        out.push(Label::send_within(
                            *model,
                            *dst,
                            *val,
                            Window::new(*lo1, *hi1),
                        ));
                        out.push(Label::send_within(
                            *model,
                            *dst,
                            *val,
                            Window::new(*lo2, *hi2),
                        ));
                    }
                },
                Op::Recv { sel, blocking } => {
                    let mk = |p: Pred| {
                        if *blocking {
                            Label::recv(p)
                        } else {
                            Label::recv_nb(p)
                        }
                    };
                    match sel {
                        Sel::Any => out.push(mk(Pred::any())),
                        Sel::Eq(s) => out.push(mk(Pred::eq(*s))),
                        Sel::EqGuard(k) => match vals[*k] {
                            Some(v) => out.push(mk(Pred::eq(resolve(v)))),
                            None => {
                                // The guard may resolve to any payload the corpus uses
                                // ("g" included — the victim's gated send), or to no value.
                                for p in ["a", "b", "g", "__none__"] {
                                    out.push(mk(Pred::eq(p)));
                                }
                            }
                        },
                    }
                }
            }
        }
        Some(out)
    }
}

// -- Generator ------------------------------------------------------------------------------

/// A near-tie delivery window (bands overlapping within 1–2 ticks) plus one late band.
fn win(rng: &mut Rng) -> (u64, u64) {
    match rng.below(5) {
        0 => (0, 1),
        1 => (1, 2),
        2 => (2, 3),
        3 => (0, 4),
        _ => (5, 6), // late: genuinely unreadable next to an unread (0,1) competitor
    }
}

fn model(rng: &mut Rng) -> Model {
    if rng.chance(50) {
        Model::Asyn
    } else {
        Model::P2p
    }
}

fn payload(rng: &mut Rng) -> &'static str {
    if rng.chance(50) {
        "a"
    } else {
        "b"
    }
}

/// One random send-ish op; guards reference `producers` (value-producing op indices so far).
fn gen_send(rng: &mut Rng, nt: usize, victim: usize, producers: &[usize]) -> Op {
    // Destination bias onto the victim thread: racing sends need a shared receiver. Kept
    // moderate — relay threads (recv → send) need incoming traffic too, or their late sends
    // (the only source of backward revisits under DES drain-first) never fire.
    let dst = if rng.chance(40) { victim } else { rng.below(nt) };
    let (lo, hi) = win(rng);
    let m = model(rng);
    let v = payload(rng);
    if !producers.is_empty() && rng.chance(55) {
        let guard = producers[rng.below(producers.len())];
        let eq = payload(rng);
        if rng.chance(50) {
            Op::SendIf {
                guard,
                eq,
                dst,
                model: m,
                val: v,
                lo,
                hi,
            }
        } else {
            let (lo2, hi2) = win(rng);
            Op::SendWin {
                guard,
                eq,
                dst,
                model: m,
                val: v,
                lo1: lo,
                hi1: hi,
                lo2,
                hi2,
            }
        }
    } else {
        Op::Send {
            dst,
            model: m,
            val: v,
            lo,
            hi,
        }
    }
}

fn gen_recv(rng: &mut Rng, producers: &[usize]) -> Op {
    let sel = match rng.below(10) {
        0..=3 => Sel::Any,
        4..=6 => Sel::Eq(payload(rng)),
        _ if !producers.is_empty() => Sel::EqGuard(producers[rng.below(producers.len())]),
        _ => Sel::Any,
    };
    Op::Recv {
        sel,
        blocking: rng.chance(70),
    }
}

/// One random program: 3–4 threads, 2–4 ops each; the last thread is the "victim", biased
/// into the consumed-competitor shape: two sequential receives followed by a value-gated
/// send (the read value decides the emission — the raft LEADER shape).
fn gen_program(rng: &mut Rng) -> VdProgram {
    let nt = 3 + rng.below(2);
    let victim = nt - 1;
    let mut threads = Vec::with_capacity(nt);
    for t in 0..nt - 1 {
        let mut ops: Vec<Op> = Vec::new();
        let mut producers: Vec<usize> = Vec::new();
        if rng.chance(60) {
            producers.push(ops.len());
            ops.push(Op::Nondet);
        }
        let _ = t;
        let ne = 1 + rng.below(3);
        for _ in 0..ne {
            match rng.below(100) {
                // A mid-thread nondet: po-after a receive it lands in `Deleted` of later
                // revisits (a nondet at op 0 is drained first by DES and is almost never
                // deleted) — this is what exercises the PASS oracle.
                0..=19 => {
                    producers.push(ops.len());
                    ops.push(Op::Nondet);
                }
                20..=64 => ops.push(gen_send(rng, nt, victim, &producers)),
                _ => {
                    // A recv guard may only reference EARLIER producers, so the fresh index
                    // is pushed after generating the op.
                    let op = gen_recv(rng, &producers);
                    producers.push(ops.len());
                    ops.push(op);
                }
            }
        }
        threads.push(ops);
    }
    // The victim thread.
    let mut ops: Vec<Op> = Vec::new();
    let mut producers: Vec<usize> = Vec::new();
    if rng.chance(40) {
        producers.push(ops.len());
        ops.push(Op::Nondet);
    }
    producers.push(ops.len());
    ops.push(Op::Recv {
        sel: Sel::Any,
        blocking: true,
    });
    if rng.chance(70) {
        // A nondet BETWEEN the two receives: po-after a blocking receive, so it sits in the
        // `Deleted` set of any revisit of that receive — the main PASS-oracle trigger.
        producers.push(ops.len());
        ops.push(Op::Nondet);
    }
    if rng.chance(80) {
        let op = gen_recv(rng, &producers);
        producers.push(ops.len());
        ops.push(op);
    }
    if rng.chance(70) {
        // The value-gated downstream send: emitted only for one read value.
        let guard = producers[rng.below(producers.len())];
        let (lo, hi) = win(rng);
        ops.push(Op::SendIf {
            guard,
            eq: payload(rng),
            dst: rng.below(nt - 1),
            model: model(rng),
            val: "g",
            lo,
            hi,
        });
    }
    threads.push(ops);
    VdProgram { threads }
}

/// A directed scaffold guaranteeing the PASS oracle fires (the §3.3 ingredients, randomized
/// in windows/models/payloads): a victim with `recv; nd; [SendIf]; recv; [SendIf]`, an early
/// sender racing a **relay** whose send is po-after its own receive — the only kind of send
/// that is late under DES drain-first and therefore backward-revisits the victim, deleting
/// the mid-nondet (a non-min holder in half the branches ⇒ an oracle call).
fn gen_scaffold(rng: &mut Rng) -> VdProgram {
    let nt = 4;
    let victim = 0usize;
    // T0 (victim): recv; nd; [SendIf gated by nd]; recv; [SendIf gated by a read].
    let mut t0: Vec<Op> = vec![
        Op::Recv {
            sel: Sel::Any,
            blocking: true,
        },
        Op::Nondet,
    ];
    if rng.chance(50) {
        // A value-gated early send between the nondet and the second receive: under one
        // value the region carries an extra competitor — the feasibility-divergence seed.
        let (lo, hi) = win(rng);
        t0.push(Op::SendIf {
            guard: 1,
            eq: payload(rng),
            dst: 1 + rng.below(nt - 1),
            model: model(rng),
            val: payload(rng),
            lo,
            hi,
        });
    }
    let second = t0.len();
    t0.push(Op::Recv {
        sel: if rng.chance(50) { Sel::Any } else { Sel::EqGuard(1) },
        blocking: true,
    });
    if rng.chance(60) {
        let (lo, hi) = win(rng);
        t0.push(Op::SendIf {
            guard: if rng.chance(50) { 1 } else { second },
            eq: payload(rng),
            dst: 1 + rng.below(nt - 1),
            model: model(rng),
            val: "g",
            lo,
            hi,
        });
    }
    // T1: the early sender racing the relay for the victim's receives.
    let (lo, hi) = win(rng);
    let t1 = vec![Op::Send {
        dst: victim,
        model: model(rng),
        val: payload(rng),
        lo,
        hi,
    }];
    // T2 (relay): recv(=x) then send to the victim — late by construction.
    let (lo, hi) = win(rng);
    let t2 = vec![
        Op::Recv {
            sel: Sel::Eq("x"),
            blocking: true,
        },
        Op::Send {
            dst: victim,
            model: model(rng),
            val: payload(rng),
            lo,
            hi,
        },
    ];
    // T3: feeds the relay.
    let (lo, hi) = win(rng);
    let t3 = vec![Op::Send {
        dst: 2,
        model: model(rng),
        val: "x",
        lo,
        hi,
    }];
    VdProgram {
        threads: vec![t0, t1, t2, t3],
    }
}

    /// Public handles for the (private, verbatim-copied) generators above.
    pub fn gen(rng: &mut Rng) -> VdProgram {
        gen_program(rng)
    }
    pub fn scaffold(rng: &mut Rng) -> VdProgram {
        gen_scaffold(rng)
    }
}

// == Corpus (в1): the DIRECTED canon-divergence generator ====================================

/// A generator aimed squarely at the rung the random corpora leave vacuous: programs on which the
/// **T2 canon behaves differently from the untimed canon**, i.e. `L1 ≠ L2`.
///
/// # Why the random corpora fail here
///
/// Arms 19/22 decide *which of several branches reaching the same `g2` may spawn it*. For that
/// decision to differ between the untimed rule and T2's, one needs a blocking receive `ep` that
/// (i) lands in a revisit's `Deleted` set, (ii) has **≥ 2** unread matching sources in
/// `G|_Previous`, and (iii) whose `(tid, idx)`-minimum is *not* the `(avail_lb, tid, idx)`-minimum
/// — either because the availability order is inverted, or because the `(tid,idx)`-min is
/// eager-infeasible / non-viable. Random soup produces (i)+(ii) rarely and (iii) almost never.
///
/// # The skeleton (a parametric family around `tests/r1_line22.rs`)
///
/// ```text
/// T0 victim : r  = recv_nb(= "L")                     — drained first by DES ⇒ stamp 0 ⇒
///                                                       everything else lands in its Deleted
/// T1 holder : ep = recv(any)                          — the arm-22 subject; 2 sources below
///             [nd = nondet{a,b}]                      — the arm-19 subject (po-after ep ⇒ Deleted)
///             [SendIf(guard) → "c" to T2, early]      — the POISON
/// T2 relay  : q  = recv(any)                          — matches both "x" and the poison "c"
///             SendIf(q == "x") → "L" to T0            — the REVISITING send
/// T3 srcs   : send(T1,"p",[a,a]); [send(T1,"q",[b,b])]; send(T2,"x",[X,X])
/// [T4]      : send(T1,"q",[b,b])                      — when the sources are split across threads
/// ```
///
/// Three knobs produce three distinct divergence mechanisms, all randomised:
///
/// * **inversion** — `avail(p)` vs `avail(q)` against their `(tid, idx)` order. Inverted, the
///   untimed canon names `p` while T2 names `q`; moreover reading the later-`avail` source with the
///   earlier one unread is eager-**infeasible**, so `cons_candidates` drops it outright.
/// * **poison on a source value** — reading the `≺`-minimal source emits an early competitor that
///   makes the relay unable to read the trigger, so the revisiting send does not exist on that
///   branch: the `≺`-min is *locally feasible but not viable*. This is the R1 mechanism, which is
///   what forces `pass_recv`'s oracle (not just its filter) to decide.
/// * **poison on a nondet value** — same, keyed on `min(S) = "a"`: the untimed arm 19 demands the
///   holder be `min(S)`, T2's PASS accepts `"b"` once `"a"` is shown non-viable. This is the shape
///   of the historical raft f1 28-vs-40 loss.
///
/// Windows are pinned (`lo == hi`) so the intended availability order is exact, and the trigger is
/// placed strictly after any poison could arrive. All candidate sends are `Asyn`: two `P2p` sends
/// on one channel would impose FIFO and collapse the two-source shape.
mod canon_corpus {
    use super::vd_corpus::{Op, Sel, VdProgram};
    use super::Rng;
    use must::event::Model;

    /// Which value emits the poison (the competitor that kills the relay's trigger read).
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Poison {
        /// No poison: the divergence must come from the availability inversion alone.
        None,
        /// Emitted when `ep` read the `(tid,idx)`-first source ("p") — the R1 shape.
        OnFirstSource,
        /// Emitted when `ep` read the `(tid,idx)`-second source ("q").
        OnSecondSource,
        /// Emitted on nondet value `"a" = min(S)` — the raft-f1 shape.
        OnNondetMin,
    }

    /// The pinned instance of the family — the deterministic twin of [`gen`], so the shape is
    /// documented and regression-guarded even if the random generator is later retuned:
    ///
    /// ```text
    /// T0: r  = recv_nb(= "L")
    /// T1: ep = recv(any);  if ep == "p" -> send(T2, "c", [0,0])      // poison
    /// T2: q  = recv(any);  if q  == "x" -> send(T0, "L", [0,0])      // revisiting send
    /// T3: send(T1,"p",[20,20]); send(T1,"q",[10,10]); send(T2,"x",[40,40])
    /// ```
    ///
    /// `p` is `(tid, idx)`-first but arrives *later* (20 vs 10), so the untimed canon names `p`
    /// while T-CANON names `q`; and reading `p` emits the poison, which beats the trigger (`arr(c)`
    /// ≤ 21 < 40), so on that branch the revisiting send never exists — `p` is locally feasible but
    /// not viable, the R1 mechanism.
    pub fn witness() -> VdProgram {
        VdProgram {
            threads: vec![
                vec![Op::Recv {
                    sel: Sel::Eq("L"),
                    blocking: false,
                }],
                vec![
                    Op::Recv {
                        sel: Sel::Any,
                        blocking: true,
                    },
                    Op::SendIf {
                        guard: 0,
                        eq: "p",
                        dst: 2,
                        model: Model::Asyn,
                        val: "c",
                        lo: 0,
                        hi: 0,
                    },
                ],
                vec![
                    Op::Recv {
                        sel: Sel::Any,
                        blocking: true,
                    },
                    Op::SendIf {
                        guard: 0,
                        eq: "x",
                        dst: 0,
                        model: Model::Asyn,
                        val: "L",
                        lo: 0,
                        hi: 0,
                    },
                ],
                vec![
                    Op::Send {
                        dst: 1,
                        model: Model::Asyn,
                        val: "p",
                        lo: 20,
                        hi: 20,
                    },
                    Op::Send {
                        dst: 1,
                        model: Model::Asyn,
                        val: "q",
                        lo: 10,
                        hi: 10,
                    },
                    Op::Send {
                        dst: 2,
                        model: Model::Asyn,
                        val: "x",
                        lo: 40,
                        hi: 40,
                    },
                ],
            ],
        }
    }

    pub fn gen(rng: &mut Rng) -> VdProgram {
        // Availability of the two candidate sources, pinned and distinct.
        let mut av_first = 5 + rng.below(15) as u64;
        let mut av_second = 5 + rng.below(15) as u64;
        if av_first == av_second {
            av_second += 3;
        }
        // Inversion: make the (tid,idx)-FIRST source the LATER-arriving one, so the untimed
        // tiebreaker and T-CANON disagree.
        let invert = rng.chance(70);
        if invert != (av_first > av_second) {
            std::mem::swap(&mut av_first, &mut av_second);
        }

        let poison = match rng.below(10) {
            0..=3 => Poison::OnFirstSource,
            4..=5 => Poison::OnSecondSource,
            6..=7 => Poison::OnNondetMin,
            _ => Poison::None,
        };
        let with_nondet = poison == Poison::OnNondetMin || rng.chance(40);
        let split = rng.chance(50);

        // T0 — the revisit victim. Non-blocking, so DES drains it at time 0 and every later event
        // falls into its `Deleted` set; reading ⊥ keeps arm 18 canonical.
        let t0 = vec![Op::Recv {
            sel: Sel::Eq("L"),
            blocking: false, // non-blocking: DES drains it at time 0
        }];

        // T1 — the holder of the two-source blocking receive.
        let mut t1: Vec<Op> = vec![Op::Recv {
            sel: Sel::Any,
            blocking: true,
        }];
        let nd_idx = if with_nondet {
            t1.push(Op::Nondet);
            Some(t1.len() - 1)
        } else {
            None
        };
        // The poison: window [0, 0..=1] measured from `fire(ep)`, so it always beats the trigger.
        let poison_hi = rng.below(2) as u64;
        match poison {
            Poison::None => {}
            Poison::OnFirstSource | Poison::OnSecondSource => t1.push(Op::SendIf {
                guard: 0,
                eq: if poison == Poison::OnFirstSource {
                    "p"
                } else {
                    "q"
                },
                dst: 2,
                model: Model::Asyn,
                val: "c",
                lo: 0,
                hi: poison_hi,
            }),
            Poison::OnNondetMin => t1.push(Op::SendIf {
                guard: nd_idx.expect("nondet present under OnNondetMin"),
                eq: "a", // = min(S) of {a, b}
                dst: 2,
                model: Model::Asyn,
                val: "c",
                lo: 0,
                hi: poison_hi,
            }),
        }

        // The trigger must arrive strictly after any poison could: `arr(c) ≤ max(av) + poison_hi`.
        let av_trigger = av_first.max(av_second) + poison_hi + 5 + rng.below(10) as u64;

        // T2 — the relay. `Sel::Any` so the poison is a genuine competitor of the trigger.
        let t2 = vec![
            Op::Recv {
                sel: Sel::Any,
                blocking: true,
            },
            Op::SendIf {
                guard: 0,
                eq: "x",
                dst: 0,
                model: if rng.chance(50) {
                    Model::Asyn
                } else {
                    Model::P2p
                },
                val: "L",
                lo: 0,
                hi: rng.below(3) as u64,
            },
        ];

        // T3 (+ T4) — the sources. Asyn: two P2p sends on the T3→T1 channel would force FIFO and
        // remove the two-candidate fork the whole shape depends on.
        let src_first = Op::Send {
            dst: 1,
            model: Model::Asyn,
            val: "p",
            lo: av_first,
            hi: av_first,
        };
        let src_second = Op::Send {
            dst: 1,
            model: Model::Asyn,
            val: "q",
            lo: av_second,
            hi: av_second,
        };
        let trigger = Op::Send {
            dst: 2,
            model: Model::Asyn,
            val: "x",
            lo: av_trigger,
            hi: av_trigger,
        };
        let mut threads = vec![t0, t1, t2];
        if split {
            // Split: the second source is on its own thread, so it is *not* in `porf(L)` and the
            // revisit deletes it — a different `Previous` for the very same tiebreaker question.
            threads.push(vec![src_first, trigger]);
            threads.push(vec![src_second]);
        } else {
            threads.push(vec![src_first, src_second, trigger]);
        }
        VdProgram { threads }
    }
}

// == Corpus (в2): the pinned R1 witness ======================================================

/// Verbatim copy of the 4-thread program of `tests/r1_line22.rs` (the first machine-confirmed
/// T2 completeness loss; its mechanism was the line-22 canon).
mod r1_witness {
    use must::event::{Label, Model, Pred, Window};
    use must::{Program, ThreadNext, Val};


type NextFn = fn(&[Option<Val>]) -> ThreadNext;
type FutureFn = fn(&[Option<Val>]) -> Option<Vec<Label>>;

pub struct Vdp {
    nexts: Vec<NextFn>,
    futures: Vec<FutureFn>,
}

impl Program for Vdp {
    fn num_threads(&self) -> usize {
        self.nexts.len()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        (0..self.nexts.len())
            .map(|i| (self.nexts[i])(&traces[i]))
            .collect()
    }
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        (self.futures[tid])(trace)
    }
}

fn is(entry: &Option<Val>, s: &str) -> bool {
    entry.as_ref() == Some(&Val::from(s))
}

// -- labels ---------------------------------------------------------------------------------

fn r_nb() -> Label {
    Label::recv_nb(Pred::eq("L"))
}
fn w_send() -> Label {
    Label::send_within(Model::Asyn, 1, "w", Window::new(100, 100))
}
fn recv_w() -> Label {
    Label::recv(Pred::eq("w"))
}
fn ep_lbl() -> Label {
    Label::recv(Pred::new("=s1|=s2", |x| x == "s1" || x == "s2"))
}
fn c_send() -> Label {
    Label::send_within(Model::Asyn, 2, "c", Window::new(0, 0))
}
fn q_lbl() -> Label {
    Label::recv(Pred::new("=m|=c", |x| x == "m" || x == "c"))
}
fn l_send() -> Label {
    Label::send(Model::Asyn, 0, "L") // untimed [0, inf)
}
fn s1_send() -> Label {
    Label::send_within(Model::Asyn, 1, "s1", Window::new(10, 10))
}
fn s2_send() -> Label {
    Label::send_within(Model::Asyn, 1, "s2", Window::new(20, 20))
}
fn m_send() -> Label {
    Label::send_within(Model::Asyn, 2, "m", Window::new(150, 150))
}

// -- threads --------------------------------------------------------------------------------

fn t0(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(r_nb()),
        _ => ThreadNext::Finished,
    }
}
fn t0_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![r_nb()],
        _ => vec![],
    })
}

fn t1(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(w_send()),
        1 => ThreadNext::Next(recv_w()),
        2 => ThreadNext::Next(ep_lbl()),
        3 if is(&trace[2], "s1") => ThreadNext::Next(c_send()),
        _ => ThreadNext::Finished,
    }
}
fn t1_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![w_send(), recv_w(), ep_lbl(), c_send()],
        1 => vec![recv_w(), ep_lbl(), c_send()],
        2 => vec![ep_lbl(), c_send()],
        3 if is(&trace[2], "s1") => vec![c_send()],
        _ => vec![],
    })
}

fn t2(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(q_lbl()),
        1 if is(&trace[0], "m") => ThreadNext::Next(l_send()),
        _ => ThreadNext::Finished,
    }
}
fn t2_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![q_lbl(), l_send()],
        1 if is(&trace[0], "m") => vec![l_send()],
        _ => vec![],
    })
}

fn t3(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(s1_send()),
        1 => ThreadNext::Next(s2_send()),
        2 => ThreadNext::Next(m_send()),
        _ => ThreadNext::Finished,
    }
}
fn t3_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![s1_send(), s2_send(), m_send()],
        1 => vec![s2_send(), m_send()],
        2 => vec![m_send()],
        _ => vec![],
    })
}

fn prog() -> Vdp {
    Vdp {
        nexts: vec![t0, t1, t2, t3],
        futures: vec![t0_future, t1_future, t2_future, t3_future],
    }
}

    /// Public handle for the (private, verbatim-copied) program above.
    pub fn program() -> Vdp {
        prog()
    }
}

// == Corpus drivers ==========================================================================

/// (а) The value-**independent** timed corpus: the first `n` programs of `tests/fuzz_timed.rs`'s
/// generator under `seed`. Structurally blind to value-steered canon divergence (that is what
/// corpus (б) is for), but it is the corpus every T2 oracle was tuned on, so a diff here would
/// contradict the existing 820-program arbitration directly.
fn run_timed_corpus(seed: u64, n: usize, name: &str) -> DeadFacts {
    let mut rng = Rng::new(seed);
    let mut facts = DeadFacts::default();
    for case in 0..n {
        let prog = timed_corpus::gen(&mut rng);
        let ctx = format!("{name} case {case}\n{:#?}", prog.threads);
        facts.add_program(&ladder_check(&ctx, || prog.clone()));
    }
    facts
}

/// (б) The value-**dependent** corpus — the one that matters. Value independence makes the
/// min-feasible canon a no-op, which is precisely how the raft f1 28-vs-40 loss and R1 stayed
/// hidden; here nondet values steer selective predicates, emission and delivery windows.
fn run_vd_corpus(seed: u64, n: usize, name: &str) -> DeadFacts {
    let mut rng = Rng::new(seed);
    let mut facts = DeadFacts::default();
    for case in 0..n {
        // Same 2-in-3 random / 1-in-3 directed-scaffold mix as the original corpus.
        let prog = if case % 3 == 2 {
            vd_corpus::scaffold(&mut rng)
        } else {
            vd_corpus::gen(&mut rng)
        };
        let ctx = format!("{name} case {case}\n{prog:#?}");
        facts.add_program(&ladder_check(&ctx, || prog.clone()));
    }
    facts
}

/// (в1) The **directed canon corpus**: [`canon_corpus::gen`] under reject sampling on the
/// `L1 ≠ L2` detector. Every candidate is fully ladder-checked (a rejected candidate is free extra
/// coverage, so nothing is wasted); only the *accepted* ones — those on which the canon actually
/// changed the search — are counted into `facts`, so the reported statistics describe the directed
/// corpus and not the sampling noise around it.
///
/// Returns `(facts over accepted programs, candidates drawn)` so the caller can report the true
/// acceptance rate rather than claim coverage it does not have.
fn run_canon_corpus(seed: u64, want: usize, cap: usize, name: &str) -> (DeadFacts, usize) {
    let mut rng = Rng::new(seed);
    let mut facts = DeadFacts::default();
    let mut drawn = 0usize;
    while facts.progs < want && drawn < cap {
        let prog = canon_corpus::gen(&mut rng);
        drawn += 1;
        let ctx = format!("{name} case {drawn}\n{prog:#?}");
        let runs = ladder_check(&ctx, || prog.clone());
        // Accept iff the canon rung actually did something: L1 and L2 disagree either in shape or
        // in *which branch* each backward revisit fired from (the canon's only job).
        let shape = |r: &LevelRun| (r.visits, r.dead, r.filtered, r.realizable_len);
        let diverged = shape(&runs[0]) != shape(&runs[1]) || runs[0].revisits != runs[1].revisits;
        if diverged {
            facts.add_program(&runs);
        }
    }
    (facts, drawn)
}

// == Tests ===================================================================================

/// (в1) The directed canon corpus — the answer to the vacuity of the `L1 ↔ L2` rung on random
/// programs (measured there: 0/250, 0/150, 2/3000, 3/2000).
///
/// Acceptance criterion agreed with the coordinator: `realizable` equal across all rungs **and**
/// a divergence rate ≥ 50 %. The rate is printed and asserted, so this test cannot silently
/// degrade into another vacuous corpus.
#[test]
fn ladder_canon_corpus() {
    check_canon_corpus(0xCA10_00DE, 300, 6000, "canon-directed 300");
}

/// Heavy: the same directed corpus, an order of magnitude wider.
#[test]
#[ignore = "heavy: 3000 canon-divergent programs x 5 rungs"]
fn ladder_canon_corpus_large() {
    check_canon_corpus(0xCA20_00DE, 3000, 60_000, "canon-directed 3000");
}

/// Shared body of the two directed-corpus tests.
fn check_canon_corpus(seed: u64, want: usize, cap: usize, name: &str) {
    let (facts, drawn) = run_canon_corpus(seed, want, cap, name);
    facts.report(name);
    let rate = 100.0 * facts.progs as f64 / drawn as f64;
    println!(
        "   canon divergence rate: {}/{drawn} candidates ({rate:.1}%)",
        facts.progs
    );
    assert_eq!(
        facts.progs, want,
        "the directed generator produced only {} divergent programs out of {drawn} candidates",
        facts.progs
    );
    assert!(
        rate >= 50.0,
        "canon divergence rate {rate:.1}% < 50% — the generator stopped hitting the shape; do NOT \
         relax this number, fix the generator (see the module docs for the three mechanisms)"
    );
}

/// (в1-pinned) The deterministic instance of the canon-divergence family. Guards the generator
/// against silently going vacuous, and documents the mechanism with exact numbers: the untimed
/// canon and T-CANON name **different** sources for `ep`, so the very same backward revisit fires
/// from a different branch on L1 than on L2 — while the realizable set is identical on all rungs.
#[test]
fn ladder_canon_shape_witness() {
    let prog = canon_corpus::witness();
    let runs = ladder_check("canon witness", || prog.clone());
    for (i, r) in runs.iter().enumerate() {
        println!(
            "   L{}: realizable={} dups={} filtered={} visits={} dead={} revisits={}",
            RUNGS[i],
            r.realizable.len(),
            r.dups,
            r.filtered,
            r.visits,
            r.dead,
            r.revisits.len()
        );
    }
    // The canon really is the thing that differs: same revisit, different source branch.
    assert_ne!(
        runs[0].revisits, runs[1].revisits,
        "the pinned witness stopped exercising the canon (L1 and L2 fire revisits from the same \
         branches) — fix the witness, do not delete the assertion"
    );
    for (i, r) in runs.iter().enumerate() {
        assert_eq!(
            r.realizable.len(),
            runs[0].realizable.len(),
            "rung L{} disagrees with zombie on the realizable count",
            RUNGS[i]
        );
    }
}

/// (а) 250 value-independent timed programs, all four rungs.
#[test]
fn ladder_timed_corpus() {
    let facts = run_timed_corpus(0x5EED_C0DE, 250, "timed");
    facts.report("timed 250");
    // Non-degeneracy: if nothing were ever filtered on L1–L3 the ladder would be comparing four
    // identical walks and could not detect anything.
    assert!(
        facts.filtered[0] > 0,
        "degenerate corpus: L1 filtered nothing, the rungs cannot differ"
    );
}

/// (б) 150 value-dependent programs, all four rungs. The corpus the historical losses needed.
#[test]
fn ladder_value_dependent_corpus() {
    let facts = run_vd_corpus(0x7D5E_ED01, 150, "value-dependent");
    facts.report("value-dependent 150");
    assert!(
        facts.filtered[0] > 0,
        "degenerate corpus: L1 filtered nothing"
    );
}

/// (в1) The 6-thread L3 counterexample (`TIME_PLAN`, "Контрпример"): the pinned shape where a
/// backward revisit lands on a feasible `G′` whose *obligatory* continuation is infeasible. It is
/// the reason T-GATE exists, so it is also the sharpest single-program test of "T-GATE loses
/// nothing": L3 (gate off) and L4 (gate on) must agree on the realizable set, and differ only in
/// how much dead work they do.
#[test]
fn ladder_l3_counterexample() {
    let prog = timed_corpus::l3_program();
    let runs = ladder_check("L3 counterexample", || prog.clone());
    for (i, r) in runs.iter().enumerate() {
        println!(
            "   L{}: realizable={} dups={} filtered={} visits={} dead={} oracle_calls={}",
            RUNGS[i],
            r.realizable.len(),
            r.dups,
            r.filtered,
            r.visits,
            r.dead,
            r.oracle_calls
        );
    }
    // Pinned by TIME_PLAN's own measurement of this program under T1 (full=2, filtered=1,
    // blocked=0). A change here means the witness stopped exercising the shape.
    assert_eq!(
        runs[0].realizable.len(),
        2,
        "L3 witness must have exactly 2 realizable terminals"
    );
    assert_eq!(
        runs[0].filtered, 1,
        "L3 witness must have exactly 1 filtered terminal on L1"
    );
    // The gate's whole purpose: no dead Visit survives it on this program.
    assert_eq!(
        runs[3].dead, 0,
        "L4 must have no dead branch on the L3 witness"
    );
}

/// (в2) The R1 witness (`tests/r1_line22.rs`): the first machine-confirmed completeness loss of
/// T2, whose mechanism was the *canon* (line 22). The ladder must therefore see it as an
/// `L1 != L2` diff if the R1 fix is ever regressed — which makes this the pinned self-test of the
/// ladder's own sensitivity to canon bugs.
#[test]
fn ladder_r1_witness() {
    let runs = ladder_check("R1 witness", r1_witness::program);
    for (i, r) in runs.iter().enumerate() {
        println!(
            "   L{}: realizable={} dups={} filtered={} visits={} dead={} oracle_calls={}",
            RUNGS[i],
            r.realizable.len(),
            r.dups,
            r.filtered,
            r.visits,
            r.dead,
            r.oracle_calls
        );
    }
    assert_eq!(
        runs[0].realizable.len(),
        3,
        "R1 witness must have 3 realizable terminals (do NOT relax — see tests/r1_line22.rs)"
    );
    // FACT, not a requirement (see `ladder_r1_l2_duplicate_witness` for the mechanism): L2 records
    // one of those three terminals twice. Pinned so a change is *noticed*; a change is a signal to
    // re-measure, not automatically a bug.
    assert_eq!(
        runs[1].dups, 1,
        "measured fact drifted: L2 used to record exactly 1 duplicate on the R1 witness"
    );
    assert_eq!(runs[2].dups, 0, "measured fact drifted: L3 dups");
}

/// The **L2 duplicate witness** — the one anomaly the ladder found, minimised to the program that
/// already exists for it.
///
/// It is *not* a divergence of realizable sets (all four rungs report the same 3 keys, asserted in
/// [`ladder_r1_witness`]): it is an optimality-(a) violation confined to the hybrid rung L2, where
/// the T2 canon runs without the pruners it presumes.
///
/// Mechanism, printed by this test:
/// * L2 explores branches L4 never reaches, because T-PRED/T-GATE are off;
/// * on one of them the line-22 PASS rule (`C1_HARDENING_SPEC` §D.5) asks whether any
///   `≺`-smaller candidate source is *viable* — and `viable_recv` says **false** for the only
///   competitor, because the branch itself is eager-infeasible;
/// * PASS is antitone in the viable set `V`: with `V = ∅` **every** reaching holder is canonical,
///   so the revisit fires from two branches and the same terminal is recorded twice (§0.7).
///
/// Direction of the error is the safe one (M1, §0.1): a duplicate, never a loss — which is why L4,
/// where the same graphs are pruned before the canon ever sees them, is unaffected (`dups = 0`).
/// Numbers pinned below are measurements of the current code, not requirements.
#[test]
#[ignore = "witness: the one L2 anomaly the ladder found (a duplicate, not a loss)"]
fn ladder_r1_l2_duplicate_witness() {
    /// Prints every `viable_recv` verdict, which is where the `V = ∅` regime becomes visible.
    struct Verdicts;
    impl Observer for Verdicts {
        fn on_viable_recv_verdict(
            &self,
            base: &ExecutionGraph,
            ep: EventId,
            src: EventId,
            revisiting: EventId,
            _rev_label: &Label,
            verdict: bool,
        ) {
            println!(
                "  viable_recv(ep={ep}, src={src}, revisiting={revisiting}) = {verdict}   \
                 base={}",
                base.canonical_key()
            );
        }
    }

    for level in [2u8, 4] {
        let obs = (ExecutionCollector::new(), Verdicts);
        println!("== level {level} ==");
        explore(
            r1_witness::program,
            &obs,
            Config::default()
                .collect_errors()
                .with_time_predicate_level(level),
        );
        let (col, _) = &obs;
        let keys = col.terminal_keys();
        let uniq: BTreeSet<&String> = keys.iter().collect();
        println!(
            "  recorded {} terminals, {} distinct",
            keys.len(),
            uniq.len()
        );
        for k in &uniq {
            let n = keys.iter().filter(|x| x == k).count();
            println!("    x{n}  {k}");
        }
        match level {
            2 => {
                assert_eq!(keys.len(), 4, "measured: L2 records 4 terminals");
                assert_eq!(uniq.len(), 3, "measured: only 3 of them are distinct");
            }
            _ => {
                assert_eq!(keys.len(), 3, "L4 must record each terminal once");
                assert_eq!(uniq.len(), 3);
            }
        }
    }
}

/// Diagnostic: run each rung of a corpus **separately**, catching panics, and report every
/// `(level, case)` that trips a debug assertion — in practice the §0.7 self-witness detector
/// (`revisit.rs`, "held nondet value is not viable ⇒ V = ∅"). This is the minimiser's entry point:
/// the four-rung `ladder_check` cannot say *which* rung panicked, and that is the whole question.
///
/// Only meaningful in a debug build (the assertion is `cfg(debug_assertions)`); in release it is
/// compiled out and this test is a slow no-op, hence `#[ignore]`.
#[test]
#[ignore = "diagnostic: locate the (level, case) of a debug-assert failure in a corpus"]
fn ladder_self_witness_probe() {
    use std::panic::{catch_unwind, AssertUnwindSafe};

    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {})); // the probe reports; the hook would just add noise
    let mut hits: Vec<(u8, usize)> = Vec::new();
    for level in LEVELS {
        let mut rng = Rng::new(0x7D5E_ED02);
        for case in 0..2000 {
            let prog = if case % 3 == 2 {
                vd_corpus::scaffold(&mut rng)
            } else {
                vd_corpus::gen(&mut rng)
            };
            let ok = catch_unwind(AssertUnwindSafe(|| {
                run_level(|| prog.clone(), level);
            }));
            if ok.is_err() {
                hits.push((level, case));
            }
        }
    }
    std::panic::set_hook(prev);
    println!("debug-assert hits (level, case): {hits:?}");
    // Before the §0.7 assertion was scoped to its premise (H) (`time_level >= 4`), this reported
    // `[(2, 333), (2, 394)]` — L2-only. It must now be empty; anything here is a finding.
    assert!(
        hits.is_empty(),
        "debug assertion fired at {hits:?} — on a coherent regime (L1/L4) that is a finding about \
         the engine, on L2/L3 it means the §0.7 scope guard regressed"
    );
}

/// The same locator as [`ladder_self_witness_probe`], on the **directed canon corpus** — the one
/// that deliberately drives the canon, and therefore the one where a debug assertion inside the
/// canon is most likely to fire. Reports every `(rung, case)` that panics.
///
/// The verdict that matters is *which rung*: on the hybrid rung L2 a red §0.7 self-witness is
/// expected (the canon is being run without the pruners that establish its precondition), whereas
/// a hit at **L4** would be a finding about the shipping regime itself.
#[test]
#[ignore = "diagnostic: locate the (rung, case) of a debug-assert failure on the canon corpus"]
fn ladder_canon_self_witness_probe() {
    use std::panic::{catch_unwind, AssertUnwindSafe};

    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut hits: Vec<(&str, usize)> = Vec::new();
    for (ri, rung) in RUNGS.iter().enumerate() {
        let mut rng = Rng::new(0xCA10_00DE);
        for case in 0..400 {
            let prog = canon_corpus::gen(&mut rng);
            let ok = catch_unwind(AssertUnwindSafe(|| {
                if ri == 4 {
                    run_l2_prime(|| prog.clone());
                } else {
                    run_level(|| prog.clone(), LEVELS[ri]);
                }
            }));
            if ok.is_err() {
                hits.push((rung, case));
            }
        }
    }
    std::panic::set_hook(prev);
    let rungs_hit: BTreeSet<&str> = hits.iter().map(|(r, _)| *r).collect();
    println!(
        "debug-assert hits: {} total, on rungs {rungs_hit:?}\n  first 20: {:?}",
        hits.len(),
        &hits[..hits.len().min(20)]
    );
    // With the §0.7 assertion scope-corrected to `time_level >= 4` (its own premise (H)), this must
    // now be empty. It was NOT empty before that correction: 36 of these 400 programs violated the
    // self-witness at L2 — the measurement that motivated the correction, reproducible by dropping
    // the `time_level < 4` guard in `revisit.rs::assert_self_witness`.
    assert!(
        hits.is_empty(),
        "debug assertion fired on {} (rung, case) pairs, rungs {rungs_hit:?} — a hit on a coherent \
         regime (L1/L4/L2′) is a finding about the engine; a hit on L2/L3 means the §0.7 scope \
         guard regressed",
        hits.len()
    );
}

/// Heavy: the `fuzz_timed` large-corpus seed extended to 3000 programs, on all four rungs.
/// (The ladder is cheap on these shapes, so the `#[ignore]` rung buys breadth, not just repetition.)
#[test]
#[ignore = "heavy: 3000-program timed corpus x 4 ladder levels"]
fn ladder_timed_corpus_large() {
    let facts = run_timed_corpus(0xA11C_C0DE, 3000, "timed-large");
    facts.report("timed 3000");
}

/// Heavy: the `fuzz_value_dependent` large-corpus seed extended to 2000 programs, on all four rungs.
///
/// Historical note: two programs of this corpus (cases 333 and 394, located by
/// [`ladder_self_witness_probe`]) used to trip the *debug-only* §0.7 self-witness assertion **at
/// level 2** — the T2 canon run on graphs T-PRED would have rejected, so the held nondet value is
/// not viable and `V = ∅`. The assertion has since been scoped to `time_level >= 4`, its own
/// premise (H); it never fired at L1, L3, **L4** or L2′ on any of the 2000 programs, which was the
/// useful half of that measurement.
#[test]
#[ignore = "heavy: 2000-program value-dependent corpus x 5 rungs"]
fn ladder_value_dependent_large() {
    let facts = run_vd_corpus(0x7D5E_ED02, 2000, "value-dependent-large");
    facts.report("value-dependent 2000");
}

/// The flag-OFF invariant, restated locally: `with_time_predicate_level(4)` must be the very same
/// configuration as `with_time_predicate()`, and level 1 the very same as `with_time_zombie()`.
/// (The ladder is a diagnostic bit; it may not change the shipping regimes.)
#[test]
fn ladder_levels_alias_the_existing_regimes() {
    let l4 = Config::default()
        .collect_errors()
        .with_time_predicate_level(4);
    let plain = Config::default().collect_errors().with_time_predicate();
    assert_eq!(l4.time_predicate, plain.time_predicate);
    assert_eq!(l4.time_predicate_level, plain.time_predicate_level);
    assert_eq!(l4.time_zombie, plain.time_zombie);
    assert_eq!(l4.time_filter, plain.time_filter);

    let l1 = Config::default()
        .collect_errors()
        .with_time_predicate_level(1);
    let zombie = Config::default().collect_errors().with_time_zombie();
    assert_eq!(l1.time_zombie, zombie.time_zombie);
    assert_eq!(l1.time_predicate, zombie.time_predicate);
    assert_eq!(l1.time_filter, zombie.time_filter);

    let untimed = Config::default();
    assert!(!untimed.time_predicate && !untimed.time_zombie && !untimed.time_filter);
}

#[test]
#[should_panic(expected = "outside 1..=4")]
fn ladder_level_zero_is_rejected() {
    let _ = Config::default().with_time_predicate_level(0);
}

#[test]
#[should_panic(expected = "outside 1..=4")]
fn ladder_level_five_is_rejected() {
    let _ = Config::default().with_time_predicate_level(5);
}
