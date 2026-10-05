//! Eager-time realizability filter for terminal execution graphs (time-intervals extension,
//! phase T1).
//!
//! The semantics below describe the legacy raw-arrival API. Explicit timed receive
//! labels select [`mailbox`]'s direct-delivery semantics instead. Call [`check_mailbox`]
//! explicitly for that contract on send-only graphs or protected restrictions that no
//! longer contain timed receives. It supports Asyn/P2p/Mbox and timed timeout/poll returns.
//!
//! An untimed-consistent terminal graph `G` (full / blocked / error) is *time-realizable*
//! when there exist arrival/fire times consistent with the eager receive semantics fixed in
//! engine_plan §0. This module compiles that semantics into a difference-constraint system
//! (solved by [`solver`]) and exposes it as a pure filter — the explorer, the consistency
//! predicates and the scheduler are untouched, because the eager semantics as a consistency
//! predicate would break Conditional Extensibility (§3.2.1) and thus Theorem 4.1.
//!
//! # The fixed semantics (engine_plan §0, verbatim intent)
//!
//! For each event `e = (t, i)`:
//! * **Clock** `Occ(e) = Fire(r*)` where `r*` is the last *blocking* receive of thread `t`
//!   with `idx < i`, else `ORIGIN` (time 0). Sends, non-blocking receives, nondet and error
//!   events do not move the clock. (Trap: this is the clock *at* `r`, `Fire` of the last
//!   blocking recv strictly before `r` — not "Occ of event idx−1".)
//! * **Arrival** of a send `s` with window `[lo, hi]` (`hi = ∞` allowed):
//!   `arr(s) ∈ [Occ(s) + lo, Occ(s) + hi]`, closed.
//! * **Visibility** `avail`: for p2p, `avail(s) = max{ arr(s″) : s″ a p2p send with the same
//!   channel `(s.tid, dst)` and `s″.idx ≤ s.idx }` (transport FIFO — an overtaking message
//!   waits in the reorder buffer). For asyn, `avail(s) = arr(s)`. Asyn sends neither gate nor
//!   are gated, even on a shared `(tid, dst)` channel (Trap b).
//! * **Blocking receive** `r` reading `s` (hard): `fire(r) ≥ avail(s)` and `fire(r) ≥ Occ(r)`,
//!   plus the binary disjunction `fire(r) = max(Occ(r), avail(s))`, expanded via `avail`:
//!   - **(A)** `avail(s) ≤ Occ(r) ∧ fire(r) = Occ(r)` — competitors are *not* checked;
//!   - **(B)** `fire(r) = avail(s) ∧ avail(s) ≥ Occ(r) ∧ ∀ competitor m′: avail(m′) ≥ avail(s)`.
//! * **Competitor** of `r` (corrected B-clause, critical): a send `m′ ≠ rf(r)` with
//!   `dst(m′) = r.tid`, matching `pred(r)`, that is *not consumed by the moment of* `r` —
//!   unread in `G`, or read by a receive `r″` with `r″.idx > r.idx` (same thread; any kind,
//!   including non-blocking). A send read by a po-earlier receive is consumed, hence not a
//!   competitor. Quantifying over "unread in the final graph" instead is a soundness bug.
//! * **Non-blocking receive** (v1 limitation): time-transparent — no fire variable, does not
//!   move the clock, its rf (⊥ included) is unconstrained by time; it participates only in
//!   the "consumed" test through its po position.
//! * All comparisons are non-strict; `∞` is the absence of an edge (no sentinel).
//!
//! # Monotonicity for fixed-choice extensions
//!
//! Extending `G` only adds hard constraints and B-disjuncts (new sends = new competitors of
//! existing receives; A-clauses are unchanged), so an eager-infeasible prefix stays
//! infeasible while those choices are retained. This does not license pruning a whole
//! MUST construction subtree: later sends can trigger backward revisits that replace
//! an old receive choice. Such pruning additionally needs construction coverage.
//!
//! # Model support (v1)
//!
//! Only Asyn and P2p carry time. [`eager_feasible`] takes a fast path (all windows untimed ⇒
//! realizable) *before* touching models, so every existing (untimed) oracle — including
//! cd/mbox — is unaffected; it panics only when a non-default window and a Cd/Mbox send are
//! both present. [`check`] always runs the full path and assumes Asyn/P2p (the guard is in
//! [`eager_feasible`]).

pub mod future;
pub mod mailbox;
pub mod solver;
pub mod witness;

pub use mailbox::{
    assert_mailbox_supported_models, check_mailbox, eager_mailbox_feasible, earliest_mailbox_times,
    verify_mailbox_schedule, Action, TimedAction,
};

use std::collections::BTreeMap;
use std::fmt;

use crate::consistency::consistent;
use crate::event::{EventId, Label, Model, Tid, Val};
use crate::graph::ExecutionGraph;
use crate::program::{Program, ThreadNext};
use crate::scheduler::traces_of;
use solver::{solve, Clause, Edge, System, VarId, Verdict, ORIGIN};

/// A time variable, indexed by its [`VarId`]. `Origin` is variable 0.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TimeVar {
    Origin,
    /// Arrival time of a send.
    Arr(EventId),
    /// Fire time of a blocking receive.
    Fire(EventId),
    /// `avail` of a p2p send with a channel prefix of ≥ 2 sends (otherwise `avail` aliases
    /// `Arr` and no variable is allocated).
    Avail(EventId),
}

/// A satisfying eager schedule. In mailbox mode, `arr` is actual delivery and `fire`
/// includes every receive completion; the legacy mode records raw arrivals and blocking
/// receives only. All values are origin-anchored (`ORIGIN` = 0) and non-negative.
#[derive(Clone, Debug, Default)]
pub struct Schedule {
    pub arr: BTreeMap<EventId, i64>,
    pub fire: BTreeMap<EventId, i64>,
    /// Complete action order for direct-mailbox schedules, including equal-time races.
    /// Empty for schedules produced by the legacy raw-arrival verifier.
    pub actions: Vec<TimedAction>,
}

/// A structured (best-effort) reason a graph is time-infeasible: the constraint atoms that
/// appear on the witnessed negative cycle. Not a minimal core — a debugging aid.
#[derive(Clone, Debug, Default)]
pub struct Explanation {
    pub atoms: Vec<ExplainAtom>,
}

/// One constraint atom, for [`Explanation`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExplainAtom {
    /// Lower window bound of send `s`.
    WindowLo(EventId),
    /// Finite upper window bound of send `s`.
    WindowHi(EventId),
    /// Gate `fire(r) ≥ avail(rf(r))` / `fire(r) ≥ Occ(r)` for receive `r` reading `s`.
    Gate { r: EventId, s: EventId },
    /// The A-clause of receive `r` ("message waited").
    BranchA(EventId),
    /// The B-clause of receive `r` ("process waited").
    BranchB(EventId),
    /// Competitor constraint `avail(m) ≥ avail(rf(r))` inside the B-clause of `r`.
    Competitor { r: EventId, m: EventId },
    /// A `max` witness of `avail(s)`: `avail(s) ≥/≤ arr(witness)`.
    AvailDef { s: EventId, witness: EventId },
    /// A timed receive's completion window.
    ReceiveWindow(EventId),
    /// A necessary causal, delivery or receive action precedence.
    MailboxOrder { before: Action, after: Action },
    /// The graph fails original MUST well-formedness or communication consistency.
    UntimedInconsistent,
}

impl fmt::Display for ExplainAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExplainAtom::WindowLo(s) => write!(f, "window-lo({s})"),
            ExplainAtom::WindowHi(s) => write!(f, "window-hi({s})"),
            ExplainAtom::Gate { r, s } => write!(f, "gate({r}←{s})"),
            ExplainAtom::BranchA(r) => write!(f, "A({r})"),
            ExplainAtom::BranchB(r) => write!(f, "B({r})"),
            ExplainAtom::Competitor { r, m } => write!(f, "competitor({r},{m})"),
            ExplainAtom::AvailDef { s, witness } => write!(f, "avail({s})≥arr({witness})"),
            ExplainAtom::ReceiveWindow(r) => write!(f, "receive-window({r})"),
            ExplainAtom::MailboxOrder { before, after } => write!(f, "{before:?} < {after:?}"),
            ExplainAtom::UntimedInconsistent => f.write_str("untimed-inconsistent"),
        }
    }
}

impl fmt::Display for Explanation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.atoms.is_empty() {
            return f.write_str("time-infeasible");
        }
        for (i, a) in self.atoms.iter().enumerate() {
            if i > 0 {
                f.write_str(" ∧ ")?;
            }
            write!(f, "{a}")?;
        }
        Ok(())
    }
}

/// The verdict of [`check`].
#[derive(Clone, Debug)]
pub enum TimedVerdict {
    Feasible(Schedule),
    Infeasible(Explanation),
}

impl TimedVerdict {
    pub fn is_feasible(&self) -> bool {
        matches!(self, TimedVerdict::Feasible(_))
    }
}

/// Whether `g` carries a timed send window at all, panicking if a timed graph also uses a
/// Cd/Mbox send (v1 supports Asyn/P2p only).
///
/// Split out of [`eager_feasible`] because the guard and the feasibility check have different
/// obligations. The check is an *invariant* under the T2 predicate, so it may be skipped where
/// the invariant is established by construction; the guard is a *precondition* of the whole
/// time extension, so it has to run on every terminal in every build profile. Left inside
/// `eager_feasible`, a release build under the predicate would never reach it and would check a
/// Cd/Mbox program silently under asyn time semantics.
pub fn assert_supported_models(g: &ExecutionGraph) -> bool {
    if g.iter_recvs().any(|r| g.label(r).is_timed_recv()) {
        assert_mailbox_supported_models(g);
        return true;
    }
    let any_timed = g
        .iter_sends()
        .any(|s| !g.send_window(s).map(|w| w.is_untimed()).unwrap_or(true));
    if !any_timed {
        return false; // fast path, ahead of the model guard: untimed graphs use any model
    }
    if let Some(s) = g
        .iter_sends()
        .find(|&s| matches!(g.send_model(s), Some(Model::Cd) | Some(Model::Mbox)))
    {
        panic!(
            "time filter (v1) supports only Asyn/P2p, but {s} is a {} send with a timed window",
            g.send_model(s).unwrap()
        );
    }
    true
}

/// Whether `g` is eager-time-realizable. The filter the explorer applies to terminals.
///
/// Fast path: if every send window is untimed (`Window::ASAP`), `g` is realizable — returned
/// *before* any model check, so untimed graphs (any models) always pass and existing oracle
/// counts are unchanged.
pub fn eager_feasible(g: &ExecutionGraph) -> bool {
    if !assert_supported_models(g) {
        return true;
    }
    check(g).is_feasible()
}

/// Full realizability check with a schedule / explanation. Explicit timed receive labels
/// dispatch to [`check_mailbox`]; otherwise this retains the legacy Asyn/P2p contract.
/// Always runs the complete path (no fast path).
pub fn check(g: &ExecutionGraph) -> TimedVerdict {
    if g.iter_recvs().any(|r| g.label(r).is_timed_recv()) {
        return check_mailbox(g);
    }
    let builder = Builder::build(g);
    match solve(&builder.system) {
        Verdict::Sat { assignment } => TimedVerdict::Feasible(builder.schedule(&assignment)),
        Verdict::Unsat { cycle, .. } => TimedVerdict::Infeasible(builder.explanation(&cycle)),
    }
}

// -- T-LB: earliest (lower-bound) times ------------------------------------------------
//
// The DES policy (T2_PLAN §2b) orders `≤_G` insertions using lower bounds on event times,
// and the time-aware canon (T2_PLAN §2d) ranks candidate sends by arrival lower bounds.
// These bounds need not be attainable in the full eager system.
// [`earliest_times`] computes them from the eager system of `g`.

/// Pointwise lower bounds from the hard-constraint relaxation of `g`'s eager system:
/// `arr(s)` and `avail(s)` for sends, `fire(r)` for blocking receives. They need not be
/// feasible times in the full system. All values are origin-anchored and non-negative.
#[derive(Clone, Debug, Default)]
pub struct Earliest {
    arr: BTreeMap<EventId, i64>,
    avail: BTreeMap<EventId, i64>,
    fire: BTreeMap<EventId, i64>,
}

impl Earliest {
    /// LB of `arr(s)`. `None` when `s` is not a send present in the graph.
    pub fn arr_lb(&self, s: EventId) -> Option<i64> {
        self.arr.get(&s).copied()
    }
    /// LB of `avail(s)` — the channel-prefix `max` for a multi-send p2p channel, else exactly
    /// `arr_lb(s)` (asyn, or a lone p2p send). `None` when `s` is not a send.
    pub fn avail_lb(&self, s: EventId) -> Option<i64> {
        self.avail.get(&s).copied()
    }
    /// LB of completion `fire(r)`. The legacy mode includes blocking receives only;
    /// [`earliest_mailbox_times`] includes every completed receive.
    pub fn fire_lb(&self, r: EventId) -> Option<i64> {
        self.fire.get(&r).copied()
    }
}

/// Lower bounds of every time variable of `g`'s eager system, or `None` when `g` is
/// eager-time-**infeasible** (no schedule exists at all).
///
/// # Feasibility uses the FULL system; the LBs use the HARD-ONLY relaxation
///
/// The `Some`/`None` split is decided by the complete disjunctive system (via [`check`]): the
/// hard core alone would call the Conditional-Extensibility counterexample feasible (its hard
/// window/gate edges are satisfiable; only the disjunctive B-clause competitor constraint is
/// not — §3.2.1, `extensibility_counterexample`). So `None` *must* be gated on the full solve.
///
/// The lower bounds themselves are the pointwise-minimum values over the hard-only relaxation
/// (drop the A/B receive clauses and the `avail` max clauses; keep the hard window / gate /
/// `avail ≥ arr` / origin edges), computed by [`Builder::earliest_lb`]. Dropping the
/// disjunctions only *relaxes* the system, so each variable's minimum there is a **sound lower
/// bound** of its true earliest time in the full system (LB ≤ true earliest — possibly not
/// tight). Note: the solver's own model is a valid schedule but *not* pointwise-minimal (slack
/// variables like `fire` come out arbitrarily high), so the LB is taken from an explicit
/// longest-path fixpoint, not from `solve`.
///
/// These bounds can be strictly loose for interval windows. For example, a process receives
/// its own `w[1,20]` and sends `c[1,1]`; another process is committed to a matching message at
/// time 20. Eager competition can require `arr(c) >= 20`, hence `fire(recv(w)) >= 19`, while
/// the hard relaxation still reports a fire lower bound of 1. Dropped competitor clauses can
/// therefore raise not just message arrivals but another process's clock through correlation.
///
/// Exactness holds in the restricted feasible, blocking-only, fixed positive-point fragment:
/// all windows are `[d,d]` with `d > 0`, pinned RF and process order determine the clocks
/// recursively, and the least hard assignment realizes that same recurrence. This special
/// case does not justify treating general interval lower bounds as attainable timestamps.
pub fn earliest_times(g: &ExecutionGraph) -> Option<Earliest> {
    if g.iter_recvs().any(|r| g.label(r).is_timed_recv()) {
        return earliest_mailbox_times(g);
    }
    let builder = Builder::build(g);
    // Feasibility: full disjunctive system (the hard core alone would be unsound — it accepts
    // the Conditional-Extensibility counterexample).
    if !solve(&builder.system).is_sat() {
        return None;
    }
    let earliest = builder.earliest_lb();
    let mut e = Earliest::default();
    for (&s, &v) in &builder.arr {
        e.arr.insert(s, earliest[v as usize]);
        e.avail.insert(s, earliest[builder.avail_ref(s) as usize]);
    }
    for (&r, &v) in &builder.fire {
        e.fire.insert(r, earliest[v as usize]);
    }
    Some(e)
}

// -- T-FC: forced-closure feasibility gate ---------------------------------------------
//
// Under the eager-as-predicate T2 (T2_PLAN §2a) a forward send or a backward revisit can land
// on a graph `g0` whose *obligatory* continuation is eager-infeasible even though `g0` itself
// is feasible (the L3 counterexample, TIME_PLAN "Дорожная карта T2"): the policy is forced by
// next_P to re-add deleted early-time sends that break the reading. The replacement for the
// refuted L3 lemma gates such a step on the feasibility not of `g0` but of its
// **forced-closure** — `g0` plus every event the policy is obliged to add *without a genuine
// rf-fork*. [`forced_closure`] builds it by a forward, revisit-free replay of `program` to
// quiescence; [`forced_closure_feasible`] then checks it with [`check`].

/// The forced-closure of `g0` under `program` (T2_PLAN §4): `g0` plus every event that the
/// forward policy is *obliged* to add with no real rf-fork, computed by a "drain to
/// quiescence" replay. Purely forward (no revisits), so it is exactly the canonical
/// completion of §4.7 truncated at the first genuine rf-fork of each thread.
///
/// Per-thread obligation (from the freshly recomputed `next` each round):
/// * `Send` / `Error` → always added (forced).
/// * `Nondet` with `|S| == 1` → add `min(S)` (forced); `|S| ≥ 2` → a value fork, stop.
/// * non-blocking `Recv` → add reading ⊥ (the nb canon, T2_PLAN §2d — nb-recv is
///   time-transparent in v1).
/// * blocking `Recv` → add reading `S` **only when `S` is statically the unavoidable
///   source** (see [`force_source`] — conditions (1)(2)(3)); otherwise stop by that thread.
/// * `Finished` / blocked → skip.
///
/// A thread that blocks earlier contributes no "ghost" events, which is exactly why the
/// forced-closure is *not* the full graph before the revisit's `restrict` (TIME_PLAN: a
/// different control flow, or an earlier block, leaves part of `Deleted` unreturned).
///
/// # C1 soundness of the blocking-receive rule
///
/// The blocking-receive rule is a **sound over-approximation**: it forces `r ← S` only when
/// `S` is provably the only source `r` could ever read *and* `r` the only consumer `S` could
/// ever have (across the whole subtree, `rf` included). A merely-unique *current* source is
/// unsafe — a competitor can be hidden behind a not-yet-forced receive (TIME_PLAN L3 review):
/// forcing it would over-prune and lose a realizable terminal (a C1 completeness violation).
/// The price is that the rule may *under*-force when a program's future is unknown
/// (`Program::possible_future` returns `None`, e.g. the coroutine runtime), leaving residual
/// dead branches — a performance matter caught by the T-GATE "≥ 1 terminal per Visit"
/// assertion, never a correctness one. Over-force is excluded by construction.
///
/// # Ordering and determinism (conjecture C2)
///
/// Sends (and the other non-recv obligations) are drained to quiescence *before* any blocking
/// receive is forced, and exactly one event is added per outer round, so a blocking receive is
/// only ever evaluated once every currently-forced send it could match is present — this rules
/// out forcing a receive before a competitor send exists. Threads are visited in a
/// deterministic order (`priorities` when a valid permutation, else `0..n`), so the closure is
/// a deterministic function of `(g0, program)`. That the *feasibility verdict* is independent
/// of this order is conjecture **C2** (T2_PLAN §6) — undecided, so it is only asserted by a
/// property test, never relied on for correctness here.
///
/// `g0` is assumed untimed-`consistent` (it always arrives from a consistent explorer state).
pub fn forced_closure<P: Program>(
    g0: &ExecutionGraph,
    program: &P,
    priorities: &[Tid],
) -> ExecutionGraph {
    let n = program.num_threads();
    let order = closure_order(priorities, n);
    let mut closure = g0.clone();
    loop {
        let traces = traces_of(&closure, n);
        let nexts = program.next(&traces);
        let mut acted = false;

        // Phase A: drain one forced non-(blocking-recv) event. Draining these before any
        // blocking receive guarantees a receive's competitor set is complete when it is forced.
        for &tid in &order {
            let ThreadNext::Next(label) = &nexts[tid] else {
                continue;
            };
            match label {
                Label::Send { .. } | Label::Error { .. } => {
                    closure.add_event(tid, label.clone());
                    acted = true;
                }
                Label::Nondet { set } if set.len() == 1 => {
                    let e = closure.add_event(tid, label.clone());
                    closure.set_nd(e, set[0]); // singleton nondet = its only value
                    acted = true;
                }
                Label::Recv {
                    blocking: false, ..
                } => {
                    let e = closure.add_event(tid, label.clone());
                    closure.set_rf(e, None); // nb-recv canon = ⊥ (T2_PLAN §2d)
                    acted = true;
                }
                // blocking recv → phase B; nondet |S| ≥ 2 → value fork, skip.
                _ => {}
            }
            if acted {
                break;
            }
        }
        if acted {
            continue;
        }

        // Phase B: force a blocking receive only when its source is STATICALLY unavoidable
        // (C1-sound rule — a merely-unique current source may hide a competitor behind a
        // not-yet-forced receive).
        for &tid in &order {
            let ThreadNext::Next(label) = &nexts[tid] else {
                continue;
            };
            if label.blocking() != Some(true) {
                continue;
            }
            if let Some(s) = force_source(&closure, program, &traces, &nexts, tid, label) {
                let e = closure.add_event(tid, label.clone());
                closure.set_rf(e, Some(s));
                acted = true;
                break;
            }
        }
        if !acted {
            break; // quiescence
        }
    }
    closure
}

/// Whether the forced-closure of `g0` under `program` is eager-time-feasible ([`check`]).
/// The gate the T2 explorer applies before a forward send (T2_PLAN §2c, line 9) or a backward
/// revisit (line 13): it rejects exactly those child `Visit`s whose obligatory continuation is
/// eager-infeasible (L3: `forced_closure(G′) = G′ + rg←g + m` is infeasible, so the revisit
/// `s → r` is rejected outright).
pub fn forced_closure_feasible<P: Program>(
    g0: &ExecutionGraph,
    program: &P,
    priorities: &[Tid],
) -> bool {
    check(&forced_closure(g0, program, priorities)).is_feasible()
}

/// The **C1-safe** eager-time gate the T2 explorer applies before a forward send (line 9) or a
/// backward revisit (line 13) — the completeness-preserving replacement for a bare
/// [`forced_closure_feasible`].
///
/// # When the forced-closure verdict may be trusted
///
/// Rejecting on `check(closure)` is sound when every constraint of `Sys(closure)` is met by the
/// schedule of every eager-realizable terminal `T` forward-reachable from `g0` — then
/// `feasible(T) ⇒ feasible(closure)`, whose contrapositive is the prune. That is exactly
/// `T2_PROOFS_A` **A2.2d** (assembled from A2.2b for "closure ⊆ T with the same labels and rf"
/// and A2.2c for the competitor conjuncts), and **A2.1b** keeps the revisits of the gated send
/// itself out of scope.
///
/// The premise A2.2d needs is that the closure made **no value-undetermined pin**. The closure's
/// pins are: a singleton nondet (one value, nothing to guess), a forced blocking read `r ← S`
/// (`force_source` fires only having proved `S` unavoidable and `r` its only possible consumer),
/// and a fresh nb-recv on `⊥` — the last being the one genuine speculation, since in `T` it may
/// read a message instead. So the trust condition is exactly `!closure_forced_nb`, and that is
/// what this function tests.
///
/// # Why exactness of `possible_future` is *not* part of the condition
///
/// Л-C1 (`C1_HARDENING_SPEC` §C.2) originally carried a side condition "exact futures". It was
/// **restated on 26.07.2026** as **per-site precision**: what the proof needs is that *at the
/// moment of each force* every unfinished thread had a `Some` future — which [`force_source`]
/// establishes constructively, since its conditions (2) and (3b) return `None` the instant they
/// meet an unfinished thread with an unknown future. An unknown future therefore never produces a
/// half-trusted closure: it makes `force_source` decline outright, the closure degenerates to a
/// pure phase-A drain, and the corresponding steps of A2.2b/A2.2d become **vacuous rather than
/// false**. A shorter closure is also harmless on its own — it only drops competitor conjuncts
/// from B-clauses, weakening `Sys(closure)`, never strengthening it.
///
/// Hence the separate `closure_is_exact` conjunct this gate used to carry was redundant, and
/// dropping it (H1) is what lets the lookahead run on the coroutine runtime at all —
/// `C1_HARDENING_SPEC` Л-G3 recorded the old behaviour ("on every `System` program the gate
/// degenerates to a raw `check(g0)`") and is retired.
///
/// Caveat on provenance: `T2_PROOFS_A` A2.2b/A2.2d still carry the older "при VI ∧ exact" stamp;
/// the corrected statements are the two dated notes in `C1_HARDENING_SPEC` §0.4 and §C.2.
///
/// # The fallback, and what is still open
///
/// The fallback branch (`check(g0)`) never over-prunes at all — `g0` infeasible ⇒ no forward
/// terminal extends it (A2.1a) — at the price of missing L3-style dead branches.
///
/// Unchanged and still open, in both branches: a *deep* revisit escaping a pruned subtree, whose
/// `g2` is not an extension of the pruned graph (global C1, `C1_HARDENING_SPEC` §D / A2.1c), and
/// the post-revisit 2-hop region of A2.2e, for which `closure_forced_nb` is the conservative
/// guard. Because of the second, this gate is applied only where a rejected child leaves the
/// backward-revisit machinery intact — line 9 (whose `backward_revisits` runs unconditionally,
/// A2.1b) and line 13 — and deliberately **not** on line 6; see the comment in
/// `Explorer::visit_nondet`.
pub fn gate_feasible<P: Program>(g0: &ExecutionGraph, program: &P, priorities: &[Tid]) -> bool {
    let closure = forced_closure(g0, program, priorities);
    if !closure_forced_nb(g0, &closure) {
        // No speculative pin: the closure is implied by every terminal extension (see above),
        // so its verdict is sound to reject on (this is what catches L3).
        check(&closure).is_feasible()
    } else {
        // The closure speculated a fresh nb-recv onto ⊥, so it may over-constrain: fall back to
        // the raw — always C1-safe — feasibility of `g0`.
        check(g0).is_feasible()
    }
}

/// Whether [`forced_closure`] itself added a **non-blocking receive** — whose `⊥` read it then
/// speculated (`forced_closure` phase A pins every fresh nb-recv to ⊥).
///
/// That ⊥ is the closure's one genuinely value-*undetermined* decision, and it is what breaks the
/// naive "the closure is a subgraph of every extension" reading of the exact gate (`T2_PROOFS_A`
/// A2.2a, cases (α)/(β)): in a real continuation the nb-recv may read a message instead, and with
/// a value-dependent body its whole po-suffix then diverges from the closure. The concrete hazard
/// (A2.2e) is a speculative ⊥-branch that emits an early-window competitor of a *kept* read,
/// making the closure infeasible while the "nb read something" branch is realizable — an
/// over-prune, i.e. a C1 completeness violation.
///
/// So the trusting branch of [`gate_feasible`] is taken only when this returns `false`. Then every
/// forced event's trace entry is determined (`None` for send/error, `min(S)` for a singleton
/// nondet, `payload(S)` for a forced read), which is the premise of Л-C1
/// (`C1_HARDENING_SPEC` §C.2, restated 26.07.2026).
///
/// Cost, honestly scoped — the two measurements are of different regimes and neither covers the
/// other:
/// * *`SeqProgram` corpus (600 programs, `C1_HARDENING_SPEC` §0.6).* Of 19 line-13 prunings none
///   rested on a forced nb, and the L3 counterexample — the demonstrated carrier of lookahead
///   value — has `forced_nb = 0`, so it still prunes. Those futures are exact, so the trust
///   condition there is the same before and after H1 and the measurement still applies.
/// * *raft (coroutine runtime).* The old "raft is untouched because the exact branch is dead
///   (Л-G3)" no longer holds — H1 retired Л-G3 and this predicate is now what decides raft's
///   gate. Measured during H1 (`--threads 1`, before the H2 memo): `closure_forced_nb` is true on
///   8/122 gate calls (`--faults 0`), 45/431 (`--faults 1`), 359/7304 (`--bug`) — the monitor's
///   pending `recv_timeout`s. It never cost a prune: on `--bug`, all 10 calls whose closure
///   verdict differed from `check(g0)` had `forced_nb = false`, and on f0/f1 no call differed at
///   all. If a cost ever shows up, the narrower certificate-based trigger is
///   `C1_HARDENING_SPEC` §C.5.
fn closure_forced_nb(g0: &ExecutionGraph, closure: &ExecutionGraph) -> bool {
    (0..closure.num_threads()).any(|t| {
        (g0.thread_len(t)..closure.thread_len(t)).any(|i| {
            matches!(
                closure.label(EventId::new(t, i)),
                Label::Recv {
                    blocking: false,
                    ..
                }
            )
        })
    })
}

// -- T2 existential canon oracle: viable(v) (T2_ORACLE_SPEC §1.3) ---------------------------
//
// The replacement for the Fix-B replay canon, dissolving its trilemma (a canon oracle cannot
// simultaneously be a deterministic forward replay, holder-independent, and exact): `viable(v)`
// is *existential* — "does SOME forward completion of the base witness the revisit with `ep`
// pinned to `v`?" — so it is holder-independent (no `g` in the signature) and exact by
// construction, at the price of a search instead of a replay. The nondet arm of
// `RevisitCondition` then PASSes a held value iff no strictly smaller value is viable
// (T2_ORACLE_SPEC §1.1), which restores the untimed min-rule whenever every value is viable.

/// Memo for [`viable`] (T2_ORACLE_SPEC §1.3 step 0). One per explorer worker, shared across
/// every oracle call of the run: the verdict of a search state is a pure function of
/// `(state content, revisiting position, revisiting label)` — plus the run-constant
/// `(program, priorities)` — so the key is `(canonical_key, revisiting, label_key(rev_label))`,
/// stamp- and order-independent (commuting resolution orders collapse onto one entry, which is
/// what makes the search effectively "by graphs, not by insertion orders").
///
/// The map is size-capped ([`VIABLE_MEMO_CAP`]): past the cap a state is simply recomputed —
/// a memo miss is never a wrong verdict. No depth cap exists anywhere in the search.
///
/// It doubles as the per-worker memo of the **gate** ([`gate_feasible_cached`], H2): the gate
/// too is a pure function of graph content under a run-constant `(program, priorities)`
/// (`C1_HARDENING_SPEC` A1.d / A3.b), and the same worker asks for it from three places — line 9
/// (`visit_send`), line 13 (`backward_revisits`) and every node of this very search. One map,
/// one lifetime, one sharding story.
#[derive(Debug, Default)]
pub struct ViableMemo {
    map: BTreeMap<(String, EventId, String), bool>,
    hits: u64,
    misses: u64,
    /// Gate verdicts by `canonical_key` (H2). Separate map: a different key type, and its hit
    /// rate is worth reading on its own.
    gate: BTreeMap<String, bool>,
    gate_hits: u64,
    gate_misses: u64,
}

/// Size cap on the [`ViableMemo`] map (entries, not bytes). Only memory, never verdicts, is
/// at stake — see the memo's docs.
const VIABLE_MEMO_CAP: usize = 1 << 20;

impl ViableMemo {
    pub fn new() -> Self {
        Self::default()
    }
    /// Search states answered from the cache.
    pub fn hits(&self) -> u64 {
        self.hits
    }
    /// Search states actually searched (cache misses).
    pub fn misses(&self) -> u64 {
        self.misses
    }
    fn get(&mut self, key: &(String, EventId, String)) -> Option<bool> {
        let got = self.map.get(key).copied();
        match got {
            Some(_) => self.hits += 1,
            None => self.misses += 1,
        }
        got
    }
    fn put(&mut self, key: (String, EventId, String), verdict: bool) {
        if self.map.len() < VIABLE_MEMO_CAP {
            self.map.insert(key, verdict);
        }
    }

    /// Gate verdicts answered from the cache (H2).
    pub fn gate_hits(&self) -> u64 {
        self.gate_hits
    }
    /// Gate verdicts actually computed (cache misses).
    pub fn gate_misses(&self) -> u64 {
        self.gate_misses
    }
    fn gate_get(&mut self, key: &str) -> Option<bool> {
        let got = self.gate.get(key).copied();
        match got {
            Some(_) => self.gate_hits += 1,
            None => self.gate_misses += 1,
        }
        got
    }
    fn gate_put(&mut self, key: String, verdict: bool) {
        if self.gate.len() < VIABLE_MEMO_CAP {
            self.gate.insert(key, verdict);
        }
    }
}

/// [`gate_feasible`] memoised by graph content (H2, `C1_HARDENING_SPEC` §E.3).
///
/// The gate is a pure function of `g0`'s content once `(program, priorities)` are fixed for the
/// run — `forced_closure` reads only `traces_of`/`next`/`consistent` (all content-addressed) and
/// [`check`] is stamp-independent (the `Builder` emits in `(tid, idx)` order) — so
/// [`ExecutionGraph::canonical_key`], the same key the explorer already trusts for dedup and for
/// the oracle memo, is a sound key. A cached verdict is therefore *identical* to a recomputed
/// one: the memo can change the run's speed, never its result.
///
/// `memo` is per worker, so parallel workers duplicate work rather than share it (H7 would lift
/// that); a miss past the size cap is simply recomputed.
pub fn gate_feasible_cached<P: Program>(
    g0: &ExecutionGraph,
    program: &P,
    priorities: &[Tid],
    memo: &mut ViableMemo,
) -> bool {
    let key = g0.canonical_key();
    if let Some(v) = memo.gate_get(&key) {
        return v;
    }
    let verdict = gate_feasible(g0, program, priorities);
    memo.gate_put(key, verdict);
    verdict
}

/// The existential viability oracle (T2_ORACLE_SPEC §1.3): whether some forward completion of
/// `base` — with the nondet `ep` re-pinned to `v` — reaches a state where the revisiting send
/// (`revisiting` at its po-position, labelled `rev_label`) is present and unread and the state
/// passes the explorer's own visitability gate ([`gate_feasible`], the O3 single predicate).
///
/// The search is an order-free DFS over *partial graphs*: each state drains every forced event
/// (send / error / singleton nondet) to quiescence, tests success, then branches over every
/// `(thread × option)` resolution of a pending choice point (blocking receive over each
/// present consistent source; non-blocking receive over those plus ⊥; nondet over each value).
/// Deferral IS the encoding of "reading a not-yet-added source": a receive is not resolved
/// until some other thread's branch has drained the sends it wants (§1.3 step 4). Commuting
/// orders collapse in the memo by `canonical_key`, so the DFS is effectively over graphs.
///
/// The verdict is a pure function of `(base, v, revisiting, rev_label, program)`: no `g`, no
/// stamps, no traversal order (O1 holder-independence). `priorities` are threaded only into
/// [`gate_feasible`] inside the success test and must not affect the verdict (asserted by
/// test, conjecture C2). Termination: bounded programs (§3.7) have finitely many partial
/// graphs and every recursion strictly grows the graph.
#[allow(clippy::too_many_arguments)]
pub fn viable<P: Program>(
    base: &ExecutionGraph,
    ep: EventId,
    v: Val,
    program: &P,
    priorities: &[Tid],
    revisiting: EventId,
    rev_label: &Label,
    memo: &mut ViableMemo,
) -> bool {
    let mut h0 = base.clone();
    h0.set_nd(ep, v);
    viable_search(h0, program, priorities, revisiting, rev_label, memo)
}

/// The receive-arm twin of [`viable`] (**R1 fix**, `C1_HARDENING_SPEC` §D.5): whether some
/// forward completion of `base` — with the blocking receive `ep` re-pinned to read `src` instead
/// of what it reads in `base` — witnesses the revisiting send present and unread.
///
/// Changing an rf edge plays exactly the role changing a nondet value plays in [`viable`]: both
/// re-pin one choice point of the base and ask whether the region can still deliver `revisiting`.
/// Everything downstream is literally the same search — the same [`viable_search`], the same
/// cuts, the same memo (whose key already distinguishes the two, since `canonical_key` encodes
/// rf), so the O2 precision argument (`T2_PROOFS_A` A1) transfers verbatim: exact under exact
/// futures, a strict under-approximation otherwise, and under-approximation is the
/// completeness-safe direction for a PASS rule (`T2_PROOFS_B` B1.d).
///
/// `src` must be present in `base`; the caller ([`crate::explorer::revisit::cons_candidates`]
/// consumers) answers "not viable" for absent candidates without calling here.
#[allow(clippy::too_many_arguments)]
pub fn viable_recv<P: Program>(
    base: &ExecutionGraph,
    ep: EventId,
    src: EventId,
    program: &P,
    priorities: &[Tid],
    revisiting: EventId,
    rev_label: &Label,
    memo: &mut ViableMemo,
) -> bool {
    let mut h0 = base.clone();
    h0.set_rf(ep, Some(src));
    viable_search(h0, program, priorities, revisiting, rev_label, memo)
}

/// The **⊥ option** of [`viable_recv`] (`pass_nb`, `T2_GAMMA_FRONTIER` §Ⅱ recipe R-1): whether
/// some forward completion of `base` — with the receive `ep` re-pinned to read **nothing** —
/// witnesses the revisiting send present and unread.
///
/// ⊥ is the `≺`-minimum option of a non-blocking receive (it *is* the untimed line-18 canon), so
/// this is the one call the non-blocking PASS rule always has to make. It is literally
/// [`viable_recv`] with `set_rf(ep, None)`: same [`viable_search`], same cuts, same memo, same O2
/// precision argument. (For a *blocking* `ep` the ⊥ state is inconsistent and the search prunes
/// it at its step 2, so calling this on one is safe but pointless.)
#[allow(clippy::too_many_arguments)]
pub fn viable_recv_bot<P: Program>(
    base: &ExecutionGraph,
    ep: EventId,
    program: &P,
    priorities: &[Tid],
    revisiting: EventId,
    rev_label: &Label,
    memo: &mut ViableMemo,
) -> bool {
    let mut h0 = base.clone();
    h0.set_rf(ep, None);
    viable_search(h0, program, priorities, revisiting, rev_label, memo)
}

/// One DFS node of [`viable`]: drain → prune → success test → branch. Takes `h` by value (the
/// callers hand over freshly built children).
fn viable_search<P: Program>(
    h: ExecutionGraph,
    program: &P,
    priorities: &[Tid],
    revisiting: EventId,
    rev_label: &Label,
    memo: &mut ViableMemo,
) -> bool {
    match viable_search_with(
        h,
        program,
        priorities,
        revisiting,
        rev_label,
        memo,
        &mut witness::NoDiagnostics,
    ) {
        Ok(verdict) => verdict,
        Err(never) => match never {},
    }
}

/// Shared search: the production controller is zero-sized and cannot stop. The diagnostic
/// controller records a concrete success and can stop without caching an incomplete result.
#[allow(clippy::too_many_arguments)]
fn viable_search_with<P: Program, C: witness::SearchControl>(
    mut h: ExecutionGraph,
    program: &P,
    priorities: &[Tid],
    revisiting: EventId,
    rev_label: &Label,
    memo: &mut ViableMemo,
    control: &mut C,
) -> Result<bool, C::Stop> {
    control.enter_state()?;
    let key = (
        h.canonical_key(),
        revisiting,
        crate::graph::label_key(rev_label),
    );
    if let Some(cached) = memo.get(&key) {
        if control.use_cached(cached) {
            return Ok(cached);
        }
    }
    let n = program.num_threads();

    // 1. DRAIN: add every forced event (send / error / singleton nondet) of every thread to
    // quiescence. The spec's per-addition consistency/feasibility cuts are subsumed by the
    // single post-drain check in step 2: a forced addition preserves consistency (a
    // ≤_G-maximal unread send is consistent in every supported model — the line-9 argument;
    // error/nondet constrain nothing), and eager-infeasibility is forward-monotone (L1-fwd),
    // so "some drain prefix infeasible" ⟺ "the quiescent state infeasible" — one solver call
    // instead of k. The label-mismatch cut stays per-addition (it is free and exits mid-drain).
    loop {
        let traces = traces_of(&h, n);
        let nexts = program.next(&traces);
        let mut acted = false;
        for (tid, next) in nexts.iter().enumerate() {
            let ThreadNext::Next(label) = next else {
                continue;
            };
            match label {
                Label::Send { .. } | Label::Error { .. } => {
                    control.add_event(true)?;
                    h.add_event(tid, label.clone());
                }
                Label::Nondet { set } if set.len() == 1 => {
                    control.add_event(true)?;
                    let e = h.add_event(tid, label.clone());
                    h.set_nd(e, set[0]);
                }
                _ => continue, // choice points wait for step 4; blocked recvs stay parked
            }
            // Mismatch cut (§1.3 step 1): the just-added event landed on `revisiting`'s
            // po-position with a different label ⇒ `s` can never appear there ⇒ no success
            // below this state.
            if tid == revisiting.tid
                && h.thread_len(tid) == revisiting.idx + 1
                && h.label(revisiting) != rev_label
            {
                memo.put(key, false);
                return Ok(false);
            }
            acted = true;
            break; // one event per round: recompute `nexts` (the program may branch)
        }
        if !acted {
            break; // quiescence
        }
    }

    let traces = traces_of(&h, n);
    let nexts = program.next(&traces);

    // 2. Permanent prunes (each condition can never be undone by a forward extension): the
    // revisiting position was passed with a wrong label (covers a mismatch already in the
    // entry state), or its thread finished short of it.
    if h.thread_len(revisiting.tid) > revisiting.idx {
        if h.label(revisiting) != rev_label {
            memo.put(key, false);
            return Ok(false);
        }
    } else if nexts[revisiting.tid].is_finished() {
        memo.put(key, false);
        return Ok(false);
    }
    // Prefix-closedness (§3.2.1 contrapositive) and L1-fwd: an inconsistent or
    // eager-infeasible state has no consistent/feasible extension — prune. This also covers
    // an inconsistent/infeasible *entry* state (e.g. `base` with `v` already contradictory).
    //
    // γ2a (C1_HARDENING_SPEC §A): the node invariant is the **gate**, not the raw `check`.
    // The explorer gates every forward send (line 9) and every revisit (line 13) on
    // `gate_feasible`, so a witness routed through a state the policy would have rejected is
    // not a witness of anything reachable — `viable` was over-approximating. Since
    // `gate_feasible ⇒ check` (Л-G1), this only *narrows* the accepting set, i.e.
    // `viable′ ⊆ viable`, and by **M1** (PASS is antitone in the viable set) no revisit that
    // fires today can stop firing; the only price is duplicates (§0.7).
    // One call per quiescent node, not per drained event. Л-G2 ("the gate is constant along a
    // drain") is **refuted** — `closure_forced_nb` is a function of the *pair* `(g0, closure)`, so
    // draining a pending `x←⊥` flips the trust branch (`C1_HARDENING_SPEC` §0.4, 26.07.2026). The
    // surviving — and sufficient — property is that the gate is **antitone** along a drain:
    // `h_i ⊆ h_k ⇒ (gate(h_k) ⇒ gate(h_i))`. Contrapositive: if any intermediate `h_i` would have
    // been rejected, the quiescent `h_k` is rejected too. So the single call at quiescence prunes
    // whenever the per-event calls would, i.e. it is at least as strong and k times cheaper
    // (§A.2). It also subsumes the old success-test conjunct, which is literally this same call on
    // this same `h`. Shares the worker's gate memo with lines 9/13 (H2).
    if !consistent(&h) || !gate_feasible_cached(&h, program, priorities, memo) {
        memo.put(key, false);
        return Ok(false);
    }

    // 3. SUCCESS (§1.4): `s` present-unread with the right label. The visitability gate — the
    // same `gate_feasible` that guards lines 9/13 (O3: one visitability predicate for canon and
    // gates) — is no longer a conjunct here: after the γ2a fix it is the *node invariant*
    // (step 2), so reaching this line already means the gate passed on this very `h`. Tested at
    // every quiescence where `s` is present-unread, not only at its emission (a mid-drain
    // success state reaches this same test at its quiescence).
    let s_present = h.thread_len(revisiting.tid) > revisiting.idx;
    if s_present && !h.is_read(revisiting) {
        control.success(&h);
        memo.put(key, true);
        return Ok(true);
    }
    // Permanent failure: `s` present but read — rf is never unset on the forward walk, so no
    // descendant can have it unread again.
    if s_present && h.is_read(revisiting) {
        memo.put(key, false);
        return Ok(false);
    }

    // 4. BRANCH over (thread × option). Every pending choice point of every thread is tried:
    // a blocking receive over each present *consistent* source (feasibility is left to the
    // child's own step-2 check — one solver call either way, and the memo dedupes), a
    // non-blocking receive over those plus ⊥, a nondet (|S| ≥ 2) over each value.
    control.branch_state();
    for (tid, next) in nexts.iter().enumerate() {
        let ThreadNext::Next(label) = next else {
            continue;
        };
        match label {
            Label::Recv { .. } => {
                control.add_event(false)?;
                let mut trial = h.clone();
                let e = trial.add_event(tid, label.clone());
                // Present sends in (tid, idx) order, then ⊥. Reading `revisiting` itself is
                // skipped: it makes `is_read(revisiting)` permanently true, so that subtree
                // can never succeed. The ⊥ option under a *blocking* receive is inconsistent
                // and filtered by the guard, exactly as in `visit_recv`.
                let mut options: Vec<Option<EventId>> = trial
                    .iter_sends()
                    .filter(|&s| s != revisiting)
                    .map(Some)
                    .collect();
                options.push(None);
                for src in options {
                    trial.set_rf(e, src);
                    if !crate::consistency::consistent_after_recv(&trial, e) {
                        continue;
                    }
                    control.branch_child();
                    if viable_search_with(
                        trial.clone(),
                        program,
                        priorities,
                        revisiting,
                        rev_label,
                        memo,
                        control,
                    )? {
                        memo.put(key, true);
                        return Ok(true);
                    }
                }
            }
            Label::Nondet { set } => {
                // set.len() >= 2 here — singletons were drained in step 1.
                control.add_event(false)?;
                let mut trial = h.clone();
                let e = trial.add_event(tid, label.clone());
                for &v2 in set.iter() {
                    trial.set_nd(e, v2);
                    control.branch_child();
                    if viable_search_with(
                        trial.clone(),
                        program,
                        priorities,
                        revisiting,
                        rev_label,
                        memo,
                        control,
                    )? {
                        memo.put(key, true);
                        return Ok(true);
                    }
                }
            }
            // Send / Error / singleton nondet cannot survive the drain to quiescence.
            _ => unreachable!("forced event at quiescence"),
        }
    }

    memo.put(key, false);
    Ok(false)
}

/// The consistent unread matching sources of a blocking receive `label` on thread `tid`,
/// evaluated against `closure` (Def 3.5(b),(c) filter overtaking p2p sources via
/// [`consistent`]). A pure query: it probes on a throwaway clone and never mutates `closure`.
///
/// `pub(crate)` because the DES scheduler (T2 §2b, [`crate::scheduler::pick`]) needs the same
/// "consistent unread matching sources" set to compute a blocking receive's `fire`-LB when it
/// decides which receive to wake.
pub(crate) fn consistent_sources(
    closure: &ExecutionGraph,
    tid: Tid,
    label: &Label,
) -> Vec<EventId> {
    let mut trial = closure.clone();
    let e = trial.add_event(tid, label.clone());
    // Candidates: unread sends to `tid` whose payload satisfies the receive predicate.
    let candidates: Vec<EventId> = closure
        .unread_sends()
        .into_iter()
        .filter(|&s| trial.matches(s, e))
        .collect();
    let mut ok = Vec::new();
    for s in candidates {
        trial.set_rf(e, Some(s));
        if consistent(&trial) {
            ok.push(s);
        }
    }
    ok
}

/// The statically-unavoidable source of blocking receive `label` on thread `tid`, or `None`
/// when forcing would risk **over-pruning** (C1). Returns `Some(S)` only when ALL hold
/// (TIME_PLAN L3 review / T2_PLAN §6 C1):
///
/// 1. `S` is the *unique* consistent unread matching source of `r` in the current `closure`;
/// 2. no unfinished thread `t ≠ tid` can emit a **future** send matching `r` (`dst = tid` ∧
///    `pred(r)`) — else a competing source may still appear, the "hidden behind a receive"
///    counterexample (a same-thread future send is po-after `r` and cannot be read by it, so
///    `tid` itself is excluded);
/// 3. `r` is the *unique* consumer of `S`: no other receive — already present on thread `tid`,
///    or a possible future receive of thread `tid` — accepts `S`'s payload. Only thread
///    `tid`'s receives can read `S` (`dst(S) = tid`), so no other thread is consulted.
///
/// Any uncertainty (`Program::possible_future` returning `None`) is read as "may match" ⇒
/// `None`. The rule may thus **under**-force (leaving residual dead branches, caught later by
/// the ≥ 1-terminal assertion) but never over-forces, so completeness (C1) is preserved.
fn force_source<P: Program>(
    closure: &ExecutionGraph,
    program: &P,
    traces: &[Vec<Option<Val>>],
    nexts: &[ThreadNext],
    tid: Tid,
    label: &Label,
) -> Option<EventId> {
    // (1) exactly one consistent unread matching source right now (0 = blocked; ≥2 = rf-fork).
    let s = match consistent_sources(closure, tid, label).as_slice() {
        [s] => *s,
        _ => return None,
    };
    let pred = label
        .pred()
        .expect("a blocking receive carries a predicate");
    let s_val = closure
        .label(s)
        .payload()
        .expect("a send carries a payload");

    // (2) no unfinished thread other than `tid` can emit a future send matching `r`.
    for (t, next) in nexts.iter().enumerate() {
        if t == tid || next.is_finished() {
            continue;
        }
        match program.possible_future(t, &traces[t]) {
            None => return None, // unknown future ⇒ a competitor may appear ⇒ don't force
            Some(future) => {
                debug_assert_eq!(
                    future.first(),
                    next.label(),
                    "possible_future contract (src/program.rs): labels[0] must be thread {t}'s \
                     next label"
                );
                let competes = future.iter().any(|l| match l {
                    Label::Send { dst, val, .. } => *dst == tid && pred.test_sym(*val),
                    _ => false,
                });
                if competes {
                    return None;
                }
            }
        }
    }

    // (3a) another receive already on thread `tid` could take `S` in a sibling terminal.
    for idx in 0..closure.thread_len(tid) {
        let l = closure.label(EventId::new(tid, idx));
        if l.is_recv() && l.pred().is_some_and(|p| p.test_sym(s_val)) {
            return None;
        }
    }
    // (3b) a possible future receive of thread `tid` (after `r`) could also accept `S`.
    match program.possible_future(tid, &traces[tid]) {
        None => return None,
        Some(future) => {
            // `future[0]` is `r` itself (the thread's next event); a *later* matching receive
            // means `S` has two possible consumers. The `.skip(1)` below is exactly where the
            // positional half of the contract is load-bearing: a head that is *not* `r` makes
            // this skip drop a real consumer, and forcing `r ← S` then over-prunes. So assert it
            // — three lines that turn "every implementation happens to comply" into a checked
            // invariant (it did **not** hold: `tests/h1_review.rs`).
            debug_assert_eq!(
                future.first(),
                Some(label),
                "possible_future contract (src/program.rs): labels[0] must be thread {tid}'s \
                 next label"
            );
            let contested = future
                .iter()
                .skip(1)
                .any(|l| l.is_recv() && l.pred().is_some_and(|p| p.test_sym(s_val)));
            if contested {
                return None;
            }
        }
    }
    Some(s)
}

/// Deterministic thread-visit order for [`forced_closure`]: `priorities` when it is a
/// permutation of `0..n`, else the identity `0..n`. (For the *verdict* the order is
/// conjectured irrelevant — C2 — but the *closure graph* is made deterministic here.)
fn closure_order(priorities: &[Tid], n: usize) -> Vec<Tid> {
    let mut seen = vec![false; n];
    let is_perm = priorities.len() == n
        && priorities
            .iter()
            .all(|&t| t < n && !std::mem::replace(&mut seen[t], true));
    if is_perm {
        priorities.to_vec()
    } else {
        (0..n).collect()
    }
}

/// Builds the difference-constraint [`System`] from a graph's canonical `(E, po, rf, windows)`
/// content, in `(tid, idx)` order (pure — independent of insertion stamps).
struct Builder<'g> {
    g: &'g ExecutionGraph,
    /// Variable meaning by id (index 0 is `Origin`).
    vars: Vec<TimeVar>,
    arr: BTreeMap<EventId, VarId>,
    fire: BTreeMap<EventId, VarId>,
    avail: BTreeMap<EventId, VarId>,
    system: System,
    /// Edge `(x, y, w)` → the atom that emitted it (best-effort; last writer wins).
    prov: BTreeMap<(VarId, VarId, i64), ExplainAtom>,
}

impl<'g> Builder<'g> {
    fn build(g: &'g ExecutionGraph) -> Self {
        let mut b = Builder {
            g,
            vars: vec![TimeVar::Origin],
            arr: BTreeMap::new(),
            fire: BTreeMap::new(),
            avail: BTreeMap::new(),
            system: System::default(),
            prov: BTreeMap::new(),
        };
        b.allocate();
        b.emit();
        b.system.n_vars =
            u32::try_from(b.vars.len()).expect("time solver variable count exceeds u32");
        b
    }

    fn alloc(&mut self, v: TimeVar) -> VarId {
        let id = VarId::try_from(self.vars.len()).expect("time solver variable count exceeds u32");
        self.vars.push(v);
        id
    }

    /// Pass 1: allocate `Arr`/`Fire`/`Avail` variables in `(tid, idx)` order.
    fn allocate(&mut self) {
        for e in self.g.iter_events() {
            let label = self.g.label(e);
            if label.is_send() {
                let id = self.alloc(TimeVar::Arr(e));
                self.arr.insert(e, id);
                // A p2p send with ≥ 2 sends on its channel prefix needs a real `max` variable;
                // otherwise `avail` aliases `Arr` (asyn, or a lone p2p send).
                if self.g.send_model(e) == Some(Model::P2p) && self.channel_prefix(e).len() >= 2 {
                    let id = self.alloc(TimeVar::Avail(e));
                    self.avail.insert(e, id);
                }
            } else if label.blocking() == Some(true) {
                let id = self.alloc(TimeVar::Fire(e));
                self.fire.insert(e, id);
            }
        }
    }

    /// The p2p channel prefix of send `s`: p2p sends `s″` with the same `(tid, dst)` and
    /// `s″.idx ≤ s.idx`, in idx order. Only meaningful for a p2p send `s`.
    fn channel_prefix(&self, s: EventId) -> Vec<EventId> {
        let dst = self.g.label(s).dst();
        (0..=s.idx)
            .map(|idx| EventId::new(s.tid, idx))
            .filter(|&s2| {
                self.g.send_model(s2) == Some(Model::P2p) && self.g.label(s2).dst() == dst
            })
            .collect()
    }

    /// `Occ(e)`: the fire variable of the last blocking receive of `e`'s thread before `e`,
    /// else `ORIGIN`. The clock *at* `e` (engine_plan §0 trap a).
    fn occ(&self, e: EventId) -> VarId {
        for idx in (0..e.idx).rev() {
            let p = EventId::new(e.tid, idx);
            if let Some(&v) = self.fire.get(&p) {
                return v;
            }
        }
        ORIGIN
    }

    /// The variable standing for `avail(s)`: the `Avail` variable when allocated, else the
    /// `Arr` variable (asyn, or a lone-prefix p2p send). `s` must be a send.
    fn avail_ref(&self, s: EventId) -> VarId {
        self.avail.get(&s).copied().unwrap_or_else(|| self.arr[&s])
    }

    /// Pointwise-minimum feasible value of every variable over the HARD edges alone, with
    /// `ORIGIN` pinned at time 0 (T-LB). A Bellman–Ford least-fixpoint of the lower bounds:
    /// each hard edge `x − y ≤ w` is equivalently `earliest[y] ≥ earliest[x] − w`, and the
    /// least assignment satisfying all of them (plus `v ≥ 0`) is the longest lower-bound path
    /// from the origin. Requires the hard core to be feasible (guaranteed when the full system
    /// is; the caller gates on that), so the fixpoint converges in `< n` passes.
    fn earliest_lb(&self) -> Vec<i64> {
        let n = self.vars.len();
        // Every variable carries an origin lower bound `v ≥ ORIGIN` (emitted in `emit`), so 0
        // is a valid starting lower bound; relaxation only raises values.
        let mut e = vec![0i128; n];
        for _ in 0..n {
            let mut changed = false;
            for edge in &self.system.hard {
                // ORIGIN is the fixed reference; never relax into it (a feasible hard core
                // never needs to, and pinning keeps every LB anchored at time 0).
                if edge.y == ORIGIN {
                    continue;
                }
                let cand = e[edge.x as usize] - i128::from(edge.w);
                if cand > e[edge.y as usize] {
                    e[edge.y as usize] = cand;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        debug_assert!(
            !self.system.hard.iter().any(|edge| {
                edge.y != ORIGIN && e[edge.x as usize] - i128::from(edge.w) > e[edge.y as usize]
            }),
            "earliest_lb did not converge (positive cycle ⇒ infeasible hard core)"
        );
        e.into_iter()
            .map(|bound| i64::try_from(bound).expect("time lower bound exceeds i64"))
            .collect()
    }

    // Edge constructors in the fixed `Edge{x,y,w} == (x − y ≤ w)` convention.
    #[inline]
    fn ge(a: VarId, b: VarId, k: i64) -> Edge {
        // a ≥ b + k  ⇔  b − a ≤ −k
        Edge { x: b, y: a, w: -k }
    }
    #[inline]
    fn le(a: VarId, b: VarId, k: i64) -> Edge {
        // a ≤ b + k  ⇔  a − b ≤ k
        Edge { x: a, y: b, w: k }
    }

    fn hard(&mut self, e: Edge, atom: ExplainAtom) {
        self.prov.insert((e.x, e.y, e.w), atom);
        self.system.hard.push(e);
    }

    /// Pass 2: emit window / avail / gate / A-B constraints in `(tid, idx)` order, then the
    /// origin lower bounds.
    fn emit(&mut self) {
        for e in self.g.iter_events() {
            let label = self.g.label(e);
            let is_send = label.is_send();
            let is_blocking_recv = label.blocking() == Some(true);
            if is_send {
                self.emit_send(e);
            } else if is_blocking_recv {
                self.emit_blocking_recv(e);
            }
            // Non-blocking receives, nondet, error: time-transparent (v1).
        }
        // Origin lower bounds: every time variable is ≥ ORIGIN (times are non-negative, and
        // this pins the earliest schedule). ORIGIN itself is skipped.
        for v in 1..self.vars.len() as VarId {
            self.hard(Self::ge(v, ORIGIN, 0), self.origin_atom(v));
        }
    }

    fn origin_atom(&self, v: VarId) -> ExplainAtom {
        // A generic-enough atom for an origin edge (only used if it lands on a cycle).
        match self.vars[v as usize] {
            TimeVar::Arr(s) | TimeVar::Avail(s) => ExplainAtom::WindowLo(s),
            TimeVar::Fire(r) => ExplainAtom::BranchA(r),
            TimeVar::Origin => ExplainAtom::BranchA(EventId::new(0, 0)),
        }
    }

    fn emit_send(&mut self, s: EventId) {
        let window = self.g.send_window(s).expect("send has a window");
        let occ = self.occ(s);
        let arr = self.arr[&s];
        // (1) window: arr ≥ occ + lo; if hi finite, arr ≤ occ + hi.
        self.hard(
            Self::ge(arr, occ, window.lo() as i64),
            ExplainAtom::WindowLo(s),
        );
        if let Some(hi) = window.hi() {
            self.hard(Self::le(arr, occ, hi as i64), ExplainAtom::WindowHi(s));
        }
        // (2) avail definition, only where a `max` variable was allocated.
        if let Some(&av) = self.avail.get(&s) {
            let prefix = self.channel_prefix(s);
            let mut alts: Vec<Vec<Edge>> = Vec::with_capacity(prefix.len());
            for &s2 in &prefix {
                let arr2 = self.arr[&s2];
                // hard: avail(s) ≥ arr(s″).
                self.hard(
                    Self::ge(av, arr2, 0),
                    ExplainAtom::AvailDef { s, witness: s2 },
                );
                // max-clause alt: avail(s) ≤ arr(s″) (exactly one holds at the maximum).
                let e = Self::le(av, arr2, 0);
                self.prov
                    .insert((e.x, e.y, e.w), ExplainAtom::AvailDef { s, witness: s2 });
                alts.push(vec![e]);
            }
            self.system.clauses.push(Clause { alts });
        }
    }

    fn emit_blocking_recv(&mut self, r: EventId) {
        let s = match self.g.reads_from(r) {
            Some(s) => s,
            None => {
                // A blocking receive reading ⊥ is untimed-inconsistent, so a terminal graph
                // never contains one (engine_plan §4.2 point 6).
                debug_assert!(false, "blocking receive {r} reads ⊥ in a terminal graph");
                return;
            }
        };
        let fire = self.fire[&r];
        let occ = self.occ(r);
        let av_s = self.avail_ref(s);

        // (3) gate: fire(r) ≥ avail(s), fire(r) ≥ Occ(r).
        self.hard(Self::ge(fire, av_s, 0), ExplainAtom::Gate { r, s });
        self.hard(Self::ge(fire, occ, 0), ExplainAtom::Gate { r, s });

        // (4) binary A/B clause.
        // A: avail(s) ≤ Occ(r) ∧ fire(r) ≤ Occ(r). Competitors are NOT checked.
        let a_alt = vec![Self::le(av_s, occ, 0), Self::le(fire, occ, 0)];
        for &e in &a_alt {
            self.prov.insert((e.x, e.y, e.w), ExplainAtom::BranchA(r));
        }
        // B: fire(r) ≤ avail(s), and avail(m′) ≥ avail(s) for each competitor m′.
        let mut b_alt = vec![Self::le(fire, av_s, 0)];
        {
            let e = b_alt[0];
            self.prov.insert((e.x, e.y, e.w), ExplainAtom::BranchB(r));
        }
        for m in self.competitors(r, s) {
            let av_m = self.avail_ref(m);
            let e = Self::ge(av_m, av_s, 0);
            self.prov
                .insert((e.x, e.y, e.w), ExplainAtom::Competitor { r, m });
            b_alt.push(e);
        }
        self.system.clauses.push(Clause {
            alts: vec![a_alt, b_alt],
        });
    }

    /// Competitors of `r` reading `s` (engine_plan §0 corrected B-clause): matching sends
    /// `m ≠ s` not consumed by the moment of `r`.
    fn competitors(&self, r: EventId, s: EventId) -> Vec<EventId> {
        self.g
            .iter_sends()
            .filter(|&m| m != s && self.g.matches(m, r) && !self.consumed_before(m, r))
            .collect()
    }

    /// Whether send `m` is consumed by the moment of `r`: read by a receive po-earlier than
    /// `r` (same thread, guaranteed by `matches` fixing `dst(m) = r.tid`). Unread, or read by
    /// a po-later receive, is *not* consumed — that is what makes it a competitor.
    fn consumed_before(&self, m: EventId, r: EventId) -> bool {
        match self
            .g
            .iter_recvs()
            .find(|&r2| self.g.reads_from(r2) == Some(m))
        {
            Some(reader) => {
                debug_assert_eq!(reader.tid, r.tid, "reader of a competitor is on r's thread");
                reader.idx < r.idx
            }
            None => false,
        }
    }

    fn schedule(&self, assignment: &[i64]) -> Schedule {
        let mut sched = Schedule::default();
        for (&e, &v) in &self.arr {
            sched.arr.insert(e, assignment[v as usize]);
        }
        for (&e, &v) in &self.fire {
            sched.fire.insert(e, assignment[v as usize]);
        }
        sched
    }

    fn explanation(&self, cycle: &[Edge]) -> Explanation {
        let mut atoms: Vec<ExplainAtom> = Vec::new();
        for e in cycle {
            if let Some(&atom) = self.prov.get(&(e.x, e.y, e.w)) {
                if !atoms.contains(&atom) {
                    atoms.push(atom);
                }
            }
        }
        Explanation { atoms }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::{Label, Model, Pred, Val, Window};
    use crate::graph::ExecutionGraph;

    fn timed(model: Model, dst: usize, val: &str, lo: u64, hi: u64) -> Label {
        Label::send_within(model, dst, val, Window::new(lo, hi))
    }

    // (i) Conditional-Extensibility counterexample: send[1,2] vs recv←m[40,60].
    #[test]
    fn extensibility_counterexample() {
        // Reading the late message m[40,60] is infeasible: competitor s[1,2] can never be
        // as-late-as m (avail(s) ≤ 2 < 40 ≤ avail(m)).
        let mut g = ExecutionGraph::new();
        let s = g.add_event(0, timed(Model::Asyn, 2, "s", 1, 2));
        let m = g.add_event(1, timed(Model::Asyn, 2, "m", 40, 60));
        let r = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r, Some(m));
        assert!(!check(&g).is_feasible());
        assert!(!eager_feasible(&g));

        // Reading the early message s is feasible (m is a free competitor: 40 ≥ 2).
        g.set_rf(r, Some(s));
        assert!(check(&g).is_feasible());
        assert!(eager_feasible(&g));
    }

    // (ii) Corrected B-clause: a po-later reader keeps x a competitor of r1.
    #[test]
    fn b_clause_late_reader_is_infeasible() {
        // r1←y[50,50], r2←x[1,1]. x is read by the po-later r2, so it is NOT consumed at r1
        // ⇒ competitor ⇒ B needs avail(x)=1 ≥ avail(y)=50, false ⇒ infeasible.
        let mut g = ExecutionGraph::new();
        let x = g.add_event(0, timed(Model::Asyn, 2, "x", 1, 1));
        let y = g.add_event(1, timed(Model::Asyn, 2, "y", 50, 50));
        let r1 = g.add_event(2, Label::recv(Pred::any()));
        let r2 = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r1, Some(y));
        g.set_rf(r2, Some(x));
        assert!(!check(&g).is_feasible());
        assert!(!eager_feasible(&g));

        // The other assignment r1←x, r2←y is feasible (x fast, then y).
        g.set_rf(r1, Some(x));
        g.set_rf(r2, Some(y));
        assert!(check(&g).is_feasible());
    }

    // (iii) P2p gating: an overtaking message waits behind its channel prefix.
    #[test]
    fn p2p_gating_makes_fire_50() {
        // T0 sends m1[50,50] then m2[1,1] on the same p2p channel to T2; T2 reads m2 first.
        // avail(m2) = max(arr(m1), arr(m2)) = 50, so fire = 50.
        let mut g = ExecutionGraph::new();
        let _m1 = g.add_event(0, timed(Model::P2p, 2, "m1", 50, 50));
        let m2 = g.add_event(0, timed(Model::P2p, 2, "m2", 1, 1));
        let r = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r, Some(m2));
        match check(&g) {
            TimedVerdict::Feasible(sched) => assert_eq!(sched.fire.get(&r), Some(&50)),
            v => panic!("expected feasible, got {v:?}"),
        }
    }

    // (iv) Asyn is neither gated nor gating, even on a shared (tid,dst) channel.
    #[test]
    fn asyn_not_gated() {
        // T0: slow[50,50], fast[1,1] (both asyn to T2); T1: mid[10,10]; T2 reads fast, mid,
        // slow in that order. Feasible — asyn does not reorder-buffer.
        let mut g = ExecutionGraph::new();
        let slow = g.add_event(0, timed(Model::Asyn, 2, "slow", 50, 50));
        let fast = g.add_event(0, timed(Model::Asyn, 2, "fast", 1, 1));
        let mid = g.add_event(1, timed(Model::Asyn, 2, "mid", 10, 10));
        let r1 = g.add_event(2, Label::recv(Pred::any()));
        let r2 = g.add_event(2, Label::recv(Pred::any()));
        let r3 = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r1, Some(fast));
        g.set_rf(r2, Some(mid));
        g.set_rf(r3, Some(slow));
        assert!(check(&g).is_feasible());
    }

    // (v) Vacuity: an untimed graph is feasible via the FULL path (not the fast path).
    #[test]
    fn untimed_graph_is_feasible_full_path() {
        let mut g = ExecutionGraph::new();
        let a = g.add_event(0, Label::send(Model::P2p, 2, "a"));
        let _b = g.add_event(1, Label::send(Model::P2p, 2, "b"));
        let r = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r, Some(a));
        assert!(check(&g).is_feasible()); // full path
        assert!(eager_feasible(&g)); // fast path
    }

    // (vi) The A-clause does NOT check competitors.
    #[test]
    fn a_clause_ignores_competitors() {
        // T1 t[100,100]→0, T2 x[10,10]→0, T3 y[20,20]→0; T0: recv(=t); recv(); recv().
        // After fire(r0)=100 both x/y arrived long ago, so each later recv fires via the
        // A-clause (message waited) regardless of the other, faster message.
        let build = |first: &str| {
            let mut g = ExecutionGraph::new();
            let r0 = g.add_event(0, Label::recv(Pred::eq("t")));
            let r1 = g.add_event(0, Label::recv(Pred::any()));
            let r2 = g.add_event(0, Label::recv(Pred::any()));
            let t = g.add_event(1, timed(Model::Asyn, 0, "t", 100, 100));
            let x = g.add_event(2, timed(Model::Asyn, 0, "x", 10, 10));
            let y = g.add_event(3, timed(Model::Asyn, 0, "y", 20, 20));
            g.set_rf(r0, Some(t));
            if first == "x" {
                g.set_rf(r1, Some(x));
                g.set_rf(r2, Some(y));
            } else {
                g.set_rf(r1, Some(y));
                g.set_rf(r2, Some(x));
            }
            g
        };
        // Both orders are feasible; a "always check competitors" bug would reject y-then-x.
        assert!(check(&build("x")).is_feasible());
        assert!(check(&build("y")).is_feasible());
    }

    // -- T-LB: earliest_times ----------------------------------------------------------

    // p2p gating: the overtaking m2's avail is the channel-prefix max = 50, so fire = 50.
    #[test]
    fn earliest_p2p_gating() {
        let mut g = ExecutionGraph::new();
        let m1 = g.add_event(0, timed(Model::P2p, 2, "m1", 50, 50));
        let m2 = g.add_event(0, timed(Model::P2p, 2, "m2", 1, 1));
        let r = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r, Some(m2));
        let e = earliest_times(&g).expect("p2p_gating is feasible");
        assert_eq!(e.arr_lb(m1), Some(50));
        assert_eq!(e.arr_lb(m2), Some(1));
        assert_eq!(e.avail_lb(m2), Some(50), "channel-prefix max");
        assert_eq!(e.avail_lb(m1), Some(50), "lone prefix at idx 0 aliases arr");
        assert_eq!(e.fire_lb(r), Some(50));
    }

    // asyn windows: avail = arr, and occ propagates the earliest fire down the receive chain.
    #[test]
    fn earliest_asyn_windows() {
        let mut g = ExecutionGraph::new();
        let slow = g.add_event(0, timed(Model::Asyn, 2, "slow", 50, 50));
        let fast = g.add_event(0, timed(Model::Asyn, 2, "fast", 1, 1));
        let mid = g.add_event(1, timed(Model::Asyn, 2, "mid", 10, 10));
        let r0 = g.add_event(2, Label::recv(Pred::any()));
        let r1 = g.add_event(2, Label::recv(Pred::any()));
        let r2 = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r0, Some(fast));
        g.set_rf(r1, Some(mid));
        g.set_rf(r2, Some(slow));
        let e = earliest_times(&g).expect("asyn windows are feasible");
        assert_eq!(e.arr_lb(fast), Some(1));
        assert_eq!(e.arr_lb(mid), Some(10));
        assert_eq!(e.arr_lb(slow), Some(50));
        assert_eq!(e.avail_lb(fast), Some(1), "asyn: avail = arr");
        // fire(r0)=max(0,1)=1; fire(r1)=max(occ=1,avail(mid)=10)=10; fire(r2)=max(10,50)=50.
        assert_eq!(e.fire_lb(r0), Some(1));
        assert_eq!(e.fire_lb(r1), Some(10));
        assert_eq!(e.fire_lb(r2), Some(50));
    }

    // A-clause: after fire(r0)=100, later receives fire at 100 via the occ gate, ignoring the
    // faster x/y — the LB must reflect that (100, not 10/20).
    #[test]
    fn earliest_a_clause_fires() {
        let mut g = ExecutionGraph::new();
        let r0 = g.add_event(0, Label::recv(Pred::eq("t")));
        let r1 = g.add_event(0, Label::recv(Pred::any()));
        let r2 = g.add_event(0, Label::recv(Pred::any()));
        let t = g.add_event(1, timed(Model::Asyn, 0, "t", 100, 100));
        let x = g.add_event(2, timed(Model::Asyn, 0, "x", 10, 10));
        let y = g.add_event(3, timed(Model::Asyn, 0, "y", 20, 20));
        g.set_rf(r0, Some(t));
        g.set_rf(r1, Some(x));
        g.set_rf(r2, Some(y));
        let e = earliest_times(&g).expect("A-clause graph is feasible");
        assert_eq!(e.arr_lb(t), Some(100));
        assert_eq!(e.fire_lb(r0), Some(100));
        assert_eq!(
            e.fire_lb(r1),
            Some(100),
            "occ(r1)=fire(r0)=100 dominates avail(x)=10"
        );
        assert_eq!(e.fire_lb(r2), Some(100));
    }

    // An eager-infeasible graph yields None (the FULL disjunctive system decides feasibility).
    #[test]
    fn earliest_none_on_infeasible() {
        let mut g = ExecutionGraph::new();
        let s = g.add_event(0, timed(Model::Asyn, 2, "s", 1, 2));
        let m = g.add_event(1, timed(Model::Asyn, 2, "m", 40, 60));
        let r = g.add_event(2, Label::recv(Pred::any()));
        g.set_rf(r, Some(m));
        assert!(
            earliest_times(&g).is_none(),
            "reading the late m is infeasible"
        );
        g.set_rf(r, Some(s));
        let e = earliest_times(&g).expect("reading the early s is feasible");
        assert_eq!(e.arr_lb(s), Some(1));
    }

    // -- T-FC: forced_closure ----------------------------------------------------------

    /// A straight-line mock program (mirrors `tests/common::SeqProgram`) for forced-closure
    /// tests: `threads[i]` is thread `i`'s ordered event list, advanced by trace length.
    struct Straight {
        threads: Vec<Vec<Label>>,
    }
    impl Program for Straight {
        fn num_threads(&self) -> usize {
            self.threads.len()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.threads
                .iter()
                .enumerate()
                .map(|(i, evs)| {
                    let done = traces[i].len();
                    if done < evs.len() {
                        ThreadNext::Next(evs[done].clone())
                    } else {
                        ThreadNext::Finished
                    }
                })
                .collect()
        }
        fn possible_future(&self, tid: Tid, trace: &[Option<Val>]) -> Option<Vec<Label>> {
            let evs = &self.threads[tid];
            Some(evs[trace.len().min(evs.len())..].to_vec())
        }
    }

    // A blocking receive with a single consistent source is forced onto the closure.
    #[test]
    fn forced_closure_forces_single_source() {
        let prog = Straight {
            threads: vec![
                vec![timed(Model::Asyn, 1, "a", 10, 20)],
                vec![Label::recv(Pred::any())],
            ],
        };
        let mut g0 = ExecutionGraph::new();
        let a = g0.add_event(0, timed(Model::Asyn, 1, "a", 10, 20));
        let closure = forced_closure(&g0, &prog, &[0, 1]);
        let r = EventId::new(1, 0);
        assert!(closure.contains(r), "the obligatory receive was forced");
        assert_eq!(closure.reads_from(r), Some(a));
        assert!(forced_closure_feasible(&g0, &prog, &[0, 1]));
    }

    // Two matching sources = a real rf-fork: the receive is NOT forced (stop by that thread).
    #[test]
    fn forced_closure_stops_on_rf_fork() {
        let prog = Straight {
            threads: vec![
                vec![Label::send(Model::Asyn, 2, "a")],
                vec![Label::send(Model::Asyn, 2, "b")],
                vec![Label::recv(Pred::any())],
            ],
        };
        let mut g0 = ExecutionGraph::new();
        g0.add_event(0, Label::send(Model::Asyn, 2, "a"));
        g0.add_event(1, Label::send(Model::Asyn, 2, "b"));
        let closure = forced_closure(&g0, &prog, &[0, 1, 2]);
        assert!(
            !closure.contains(EventId::new(2, 0)),
            "the contested receive must not be forced"
        );
        // No receive in the closure ⇒ vacuously time-feasible.
        assert!(forced_closure_feasible(&g0, &prog, &[0, 1, 2]));
    }

    /// The 6-thread L3 program (TIME_PLAN "Контрпример"), shared by the L3 tests.
    fn l3_program() -> Straight {
        Straight {
            threads: vec![
                vec![Label::recv(Pred::any())],           // T0: r = recv(any)
                vec![timed(Model::Asyn, 0, "a", 1, 100)], // T1: a
                vec![
                    Label::recv(Pred::eq("g")),
                    timed(Model::Asyn, 0, "b0", 0, 0),
                ], // T2: rg; m
                vec![timed(Model::Asyn, 2, "g", 5, 5)],   // T3: g
                vec![Label::recv(Pred::eq("x")), timed(Model::Asyn, 0, "b", 0, 0)], // T4: rs; s
                vec![timed(Model::Asyn, 4, "x", 30, 30)], // T5: x
            ],
        }
    }

    // L3: G′ = {a, g, x, r←s, rs←x, s} is eager-feasible on its own, but its forced-closure
    // re-adds rg←g and m and is infeasible (avail(m)=5 ≥ avail(s)=30 is false) ⇒ the revisit
    // s→r is rejected. This is the regression that a T1-style terminal-count check misses.
    #[test]
    fn forced_closure_l3_counterexample() {
        let prog = l3_program();
        let prio: Vec<usize> = (0..6).collect();

        let mut g = ExecutionGraph::new();
        let r = g.add_event(0, Label::recv(Pred::any()));
        let _a = g.add_event(1, timed(Model::Asyn, 0, "a", 1, 100));
        let _gg = g.add_event(3, timed(Model::Asyn, 2, "g", 5, 5));
        let rs = g.add_event(4, Label::recv(Pred::eq("x")));
        let s = g.add_event(4, timed(Model::Asyn, 0, "b", 0, 0));
        let x = g.add_event(5, timed(Model::Asyn, 4, "x", 30, 30));
        g.set_rf(r, Some(s));
        g.set_rf(rs, Some(x));

        assert!(consistent(&g), "G′ must be untimed-consistent");
        assert!(check(&g).is_feasible(), "G′ alone is eager-feasible");

        let closure = forced_closure(&g, &prog, &prio);
        assert!(closure.contains(EventId::new(2, 0)), "rg is forced");
        assert!(closure.contains(EventId::new(2, 1)), "m is forced");
        assert_eq!(
            closure.reads_from(EventId::new(2, 0)),
            Some(EventId::new(3, 0)),
            "rg reads g"
        );
        assert!(
            !forced_closure_feasible(&g, &prog, &prio),
            "L3: the obligatory rg←g + m makes the closure infeasible"
        );

        // C2 (order independence of the verdict): every thread-visit order agrees.
        for perm in perms6() {
            assert!(
                !forced_closure_feasible(&g, &prog, &perm),
                "verdict must not depend on the force-add order (perm {perm:?})"
            );
        }
    }

    // C1 regression (must-expert): a blocking receive with a *currently*-unique source must
    // NOT be forced when a competitor is hidden behind an unforced receive — forcing r←S here
    // would over-prune the realizable terminal r←m, r2←S.
    //   T0: r=recv(=v); r2=recv(=v)   T1: S=send(T0,"v",[30,30])
    //   T2: rk=recv(=k); m=send(T0,"v",[1,1])   T3: k=send(T2,"k",[0,0])
    #[test]
    fn forced_closure_c1_hidden_competitor_not_forced() {
        let prog = Straight {
            threads: vec![
                vec![Label::recv(Pred::eq("v")), Label::recv(Pred::eq("v"))],
                vec![timed(Model::Asyn, 0, "v", 30, 30)],
                vec![Label::recv(Pred::eq("k")), timed(Model::Asyn, 0, "v", 1, 1)],
                vec![timed(Model::Asyn, 2, "k", 0, 0)],
            ],
        };
        let empty = ExecutionGraph::new();
        let prio = [0, 1, 2, 3];

        // r is C1-unsafe to force: S has a hidden competitor (m, behind rk) AND a second
        // possible consumer (r2). The closure leaves thread 0 untouched.
        let closure = forced_closure(&empty, &prog, &prio);
        assert_eq!(
            closure.thread_len(0),
            0,
            "the C1-unsafe receive r must not be forced"
        );
        // rk←k IS force-safe, so the closure still drains T2/T3.
        assert!(
            closure.contains(EventId::new(2, 1)),
            "m is drained after rk←k"
        );

        // The gate must NOT reject Visit(∅): the subtree holds a realizable terminal.
        assert!(
            forced_closure_feasible(&empty, &prog, &prio),
            "C1: the gate must not over-prune"
        );

        // Witness that realizable terminal (r←m, r2←S) directly.
        let mut term = ExecutionGraph::new();
        let r = term.add_event(0, Label::recv(Pred::eq("v")));
        let r2 = term.add_event(0, Label::recv(Pred::eq("v")));
        let s_big = term.add_event(1, timed(Model::Asyn, 0, "v", 30, 30));
        let rk = term.add_event(2, Label::recv(Pred::eq("k")));
        let m = term.add_event(2, timed(Model::Asyn, 0, "v", 1, 1));
        let k = term.add_event(3, timed(Model::Asyn, 2, "k", 0, 0));
        term.set_rf(rk, Some(k));
        term.set_rf(r, Some(m));
        term.set_rf(r2, Some(s_big));
        assert!(consistent(&term));
        assert!(
            check(&term).is_feasible(),
            "r←m, r2←S is a realizable terminal the gate must preserve"
        );
    }

    // L3 terminals: r←a and r←m are realizable; the full r←s is not (check by itself).
    #[test]
    fn forced_closure_l3_terminals() {
        let prog = l3_program();
        let prio: Vec<usize> = (0..6).collect();

        // Build the full terminal reading `which` of {a, b0, b} at r.
        let terminal = |which: &str| {
            let mut g = ExecutionGraph::new();
            let r = g.add_event(0, Label::recv(Pred::any()));
            let a = g.add_event(1, timed(Model::Asyn, 0, "a", 1, 100));
            let rg = g.add_event(2, Label::recv(Pred::eq("g")));
            let m = g.add_event(2, timed(Model::Asyn, 0, "b0", 0, 0));
            let gg = g.add_event(3, timed(Model::Asyn, 2, "g", 5, 5));
            let rs = g.add_event(4, Label::recv(Pred::eq("x")));
            let s = g.add_event(4, timed(Model::Asyn, 0, "b", 0, 0));
            let x = g.add_event(5, timed(Model::Asyn, 4, "x", 30, 30));
            g.set_rf(rg, Some(gg));
            g.set_rf(rs, Some(x));
            let src = match which {
                "a" => a,
                "b0" => m,
                "b" => s,
                _ => unreachable!(),
            };
            g.set_rf(r, Some(src));
            g
        };

        // r←a: complete terminal, forced-closure = itself, feasible (arr(a) ∈ [1,5]).
        let ta = terminal("a");
        assert!(consistent(&ta));
        assert!(forced_closure_feasible(&ta, &prog, &prio), "r←a realizable");
        // r←b0 (= r←m): realizable.
        let tm = terminal("b0");
        assert!(forced_closure_feasible(&tm, &prog, &prio), "r←m realizable");
        // r←b (= r←s): infeasible by itself (competitor m=5 < avail(s)=30).
        let ts = terminal("b");
        assert!(!check(&ts).is_feasible(), "the full r←s is time-infeasible");
        assert!(!forced_closure_feasible(&ts, &prog, &prio));
    }

    /// A small fixed set of 6-thread visit orders for the C2 order-independence check:
    /// identity, reverse, and a rotation.
    pub(super) fn perms6() -> Vec<Vec<usize>> {
        vec![
            (0..6).collect(),
            (0..6).rev().collect(),
            vec![2, 3, 4, 5, 0, 1],
        ]
    }
}
