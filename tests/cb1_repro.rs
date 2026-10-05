//! C-B1 (risk R5 / recipe §B1.f-1) — machine verification of an optimality-(a) DUPLICATE
//! candidate for the T2 eager-time-predicate canon.
//!
//! RESULT: **NO-REPRO — SHARPENED.** No directed shape and no program in a large C-B1-biased
//! *and* survivor-inversion-biased randomized corpus (65 000+ programs, four generator
//! families) produces a duplicate T2 terminal key; T2's realizable `full_keys` set equals the
//! T1-filter reference on every program (completeness intact throughout).
//!
//! This supersedes the first NO-REPRO, whose load-bearing lemma — "the DES insertion stamp
//! order of `g_add` is LB-monotone (`stamp(x) ≤ stamp(y) ⇒ LB(x) ≤ LB(y)`)" — an adversarial
//! review **refuted** (it is TRUE only on forward segments; a post-`restrict` re-stamp breaks
//! it, the committed F3 certificate). This file *builds* the refuted shape and reports:
//!
//!   * **The stamp INVERSION `stamp(r'') ≤ stamp(ep)` with `r''` late-fire and `ep` low-LB IS
//!     reachable** — [`cb1_survivor_inversion_no_dup`] witnesses 60+ of them across the corpus,
//!     directly contradicting the old proof's "`restrict` preserves insertion order ⇒ no
//!     inversion can flip it". So the inversion is NOT the obstruction.
//!   * **The C-B1 *mechanism* is real and WOULD duplicate** if its state were reachable:
//!     [`cb1_mechanism_positive_control`] hand-builds the exact `g_add` (`r''←w` late, `S`
//!     early-unread competitor, nondet `ep ∈ Deleted`) and shows [`must::time::viable`] is
//!     uniform-FALSE over *both* nondet values ⇒ the min-holder passes trivially AND every
//!     non-min holder passes ⇒ two branches emit the same `ep`-free `g2` ⇒ a duplicate.
//!   * **The residual obstruction is DIFFERENT and deeper: the C-B1 root precondition — an
//!     eager-INFEASIBLE `g_add` at a revisit — is forward-unreachable**, because the DES
//!     *drain-first* discipline (Lemma 1 / L-DES-1) guarantees a maximal newly-added send `S`
//!     has `avail(S) ≥` the source-`avail` of every already-woken blocking receive, so `S` is
//!     never a *violating* competitor: **`g_add = feasible-g + one maximal send` is ALWAYS
//!     eager-feasible.** Witnessed: `infeas_send_add == 0` over the ~200 000 maximal-send
//!     additions of the survivor corpus (release), plus every send addition of the older
//!     `gen_cb1` corpus. On a feasible `g_add` the min-holder's "`g` is its own witness" pass is
//!     *justified*, and `viable(min)` comes out TRUE (the base + `S`-unread is a feasible
//!     prefix), so the non-min holder is correctly rejected — no second firing, no duplicate.
//!   * **The alternate re-stamp route that could smuggle in an infeasible `g_add` is barred by
//!     line 21**: it needs a prior revisit whose revisiting send `s1` keeps `r''` as a survivor
//!     via `r'' ∈ porf(s1)`; but `s1` (read by that revisit's victim `r1`, `stamp(r1) <
//!     stamp(s1)`) then lands in the *later* revisit's `Deleted`, where line 21 rejects it
//!     (`r1 ∈ Previous(s1)` reads `s1`). A revisiting send can never sit in a later revisit's
//!     `Deleted`.
//!
//! So of the recipe's four ingredients — {stamp inversion, low-LB nondet in `Deleted∩Previous`,
//! base-localized `g_add` infeasibility healed in `g2`, ≥2 reaching holders} — the first,
//! second and fourth ARE assembled (and the PASS mechanism proven live); only the **third**
//! cannot be, and its impossibility is the drain-first feasibility invariant (orthogonal to the
//! refuted stamp lemma), corroborated by line 21 on the sole re-stamp escape.
//!
//! =====================================================================================
//! # The mechanism under test (recipe §B1.f-1) — first NO-REPRO's reasoning, kept for record
//!
//! (The sub-case analysis below is retained verbatim from the first attempt; its *conclusion*
//! stands but its stamp-monotonicity *proof* is refuted — see the SHARPENED result above. The
//! `cb1_machine_verification` test it documents still passes and is still a valid regression.)
//!
//! The nondet PASS rule (`src/explorer/revisit.rs`, `Label::Nondet` arm of `revisit_condition`)
//! passes a holder `v_held` iff **no strictly-smaller value `v` is `viable(base, ep, v, …)`**,
//! where `base = viability_base(g, ep, porf_s) = Previous(ep) \ cone(ep)`. A duplicate arises iff
//! `viable(v) = false` for EVERY value below the held one at ≥ 2 holders of one nondet `ep` that
//! lies in `Deleted` of a backward revisit `(r, s)` — then every holder PASSes, and because the
//! revisit deletes `ep` (it is in `Deleted`), the two branches produce the **same** value-free
//! `g2` ⇒ the same canonical key is visited twice. (Completeness is untouched: the min holder
//! always PASSes, so the terminal is never lost — the oracle is one-sided, it can only duplicate.)
//!
//! `viable(min) = false` means every forward completion of `base` with `s` present-**unread** is
//! eager-infeasible. An unread send `s` can only make a graph infeasible as a *competitor* of some
//! blocking receive `r''` (matching `s`, `dst(s)=r''.tid`, not consumed before `r''`) whose B-clause
//! it violates while the A-clause fails — the sole channel by which an unread send touches the time
//! system. For the revisit to nonetheless *heal* this (so `g2` is feasible and the revisit fires),
//! `s` must become consumed by `r` or `r''` must be deleted. If `r''` is po-EARLIER than `r` it is
//! kept and stays a competitor ⇒ the line-13 gate rejects `g2` ⇒ no dup (safe sub-case i). If
//! `r'' ∈ porf(s)` then `⟨r,s⟩ ∈ porf` and `r` is not a revisit candidate (safe sub-case ii). So the
//! ONLY dangerous sub-case is:
//!
//!   * `r''` blocking, po-LATER than `r`, `r'' ∈ Deleted ∩ base` (i.e. `stamp(r) < stamp(r'') ≤
//!     stamp(ep)`, `r'' ∉ cone(ep)`), reading a LATE-avail source `w`, with `s` a FORCED-violating
//!     early competitor (`avail_max(s) < avail_lb(w)`). Then in `base` `r''` is kept reading `w`,
//!     so every re-emission of `s` in the `viable` search re-creates the conflict ⇒ `viable = false`
//!     uniformly; in `g2` `r''` is deleted ⇒ `g2` feasible ⇒ the revisit fires from every holder.
//!
//! # Why the dangerous sub-case cannot be assembled (the blocking invariant)
//!
//! Work in the DES insertion order `≤_G` used under `with_time_predicate` (`scheduler::pick_des`):
//!   * a send `s` is inserted at `LB(s) = occ_lb(s) + lo(s) = arr_lb(s)`, and for the timed models
//!     (Asyn / lone-p2p) `avail_lb(s) = arr_lb(s) = LB(s)`; a blocking receive `r''` is woken at
//!     `LB(r'') = fire_lb(r'') = max(occ_lb(r''), avail_lb(w)) ≥ avail_lb(w)` (phase A drains every
//!     addable send/nondet before phase B ever wakes a blocking receive);
//!   * `restrict` re-stamps survivors **in old-stamp order** (`graph.rs`), so no backward revisit
//!     can invert the relative `≤_G` of two survivors (the claimed "2-hop inversion" cannot flip it).
//!
//! Now chain the four requirements of the dangerous sub-case:
//!   (a) `ep ∈ Deleted` with `s` the maximal (just-added) revisiting event ⇒ `stamp(s) > stamp(ep)`
//!       ⇒ `LB(s) ≥ LB(ep)`;
//!   (b) `r'' ∈ base = Previous(ep)` ⇒ `stamp(r'') ≤ stamp(ep)` ⇒ `LB(r'') ≤ LB(ep)`;
//!   (c) `LB(r'') = fire_lb(r'') ≥ avail_lb(w)`;
//!   (d) forced competitor violation ⇒ `avail_max(s) < avail_lb(w)`, and always `LB(s) = arr_lb(s)
//!       ≤ avail_max(s)`.
//!
//! Chaining (d)→(c)→(b)→(a):  `LB(s) ≤ avail_max(s) < avail_lb(w) ≤ LB(r'') ≤ LB(ep) ≤ LB(s)`,
//! i.e. `LB(s) < LB(s)` — a contradiction. Intuitively: the very earliness that lets `s` violate
//! `r''`'s late read (small `avail`) also forces `s` to be *inserted early* (small stamp), so `s`
//! cannot be the maximal send that deletes both `ep` and `r''`; and since `restrict` preserves
//! insertion order, no prior revisit can promote an early-`avail` `s` to a late stamp. The dangerous
//! shape therefore degenerates to one of the safe landings: `r''` is absent from `g_add` (its late
//! wake put it after `s`), or `s`'s `avail` is NOT forced below `w`'s (`g_add` feasible, so
//! `viable(min)=true`), or `r''` is po-earlier/kept (gate rejects `g2`). All three are observed
//! below; none duplicates.
//!
//! # What is asserted here
//!
//! * A directed System build of the recipe scaffold + the "5th ingredient" (a po-late blocking
//!   `r''` on the monitor reading a late `w`, with an early-windowed `L`): no dup, T2==T1.
//! * A large C-B1-biased randomized corpus over an exact-`possible_future` table program
//!   (`VdProgram`, the regime in which the dedup argument is stated, so `gate`/`viable` are exact):
//!   completeness (`T2 full == T1 full`) and zombie-agreement on EVERY program, and **no** T2
//!   duplicate on any. Coverage floors ensure the corpus actually exercises the nondet-in-`Deleted`
//!   revisit and the non-min PASS oracle (incl. its false path).
//! * An empirical obstruction check (`is_dangerous`, evaluated on the real pre-`restrict` `g_add`
//!   with real stamps): the count of revisits whose `Deleted` carries a nondet AND a po-later
//!   blocking `r''` with `stamp(r'') ≤ stamp(ep)` while `g_add` is eager-infeasible is **0** — the
//!   stamp inequality of the proof, witnessed.
//!
//! A T2-vs-T1 `full_keys` divergence would be a *completeness* finding (far more serious than a
//! duplicate) and is asserted against loudly; none occurs.
//!
//! # Empirical FINDING (release run, 5000 random + 4 directed programs)
//!
//! ```text
//! revisits=10824  nd_in_Deleted_revisits=2001  nd+po-later-r''_revisits=1229
//! viable_calls=3400  viable_false=319  dangerous=0  DUPLICATES=0
//! (T2 full == T1 full and zombie == T1 on every one of the 5004 programs)
//! ```
//!
//! The dangerous *shape* (a nondet AND a po-later blocking `r''` both in `Deleted`) is explored
//! 1229 times and the non-min PASS oracle's FALSE path fires 319 times, so the corpus genuinely
//! drives the mechanism — yet the FULL dangerous configuration (`stamp(r'') ≤ stamp(ep)` with an
//! eager-infeasible `g_add`) arises **zero** times, and not one duplicate is produced. Concretely,
//! every directed/random attempt to make `r''` read a late-avail source with a low stamp lands in a
//! safe case: `r''` fires late and is inserted after the revisiting `L` (absent from `base`), or the
//! send that makes `L` the maximal revisiting event (a large `Occ` from its relay chain) also lifts
//! `avail(L)` above `avail(w)` so `L` is not a violating competitor (`g_add` feasible,
//! `viable(min)=true`). This is the LB contradiction above, observed.

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::sync::Mutex;

use must::event::{EventId, Label, Model, Pred, Window};
use must::graph::ExecutionGraph;
use must::intern::resolve;
use must::{
    explore, Config, Ctx, ExecutionCollector, Observer, Program, System, ThreadNext, Val,
};

// =====================================================================================
// Value-dependent table program with an EXACT possible_future (copied, self-contained,
// from tests/gamma4_repro.rs / tests/fuzz_value_dependent.rs).
// =====================================================================================

#[derive(Clone, Copy, Debug)]
enum Sel {
    Any,
    Eq(&'static str),
}

#[derive(Clone, Debug)]
enum Op {
    Nondet,
    Send {
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    SendIf {
        guard: usize,
        eq: &'static str,
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
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

#[derive(Clone, Debug)]
struct VdProgram {
    threads: Vec<Vec<Op>>,
}

fn guard_hits(vals: &[Option<Val>], k: usize, eq: &str) -> bool {
    vals[k].is_some_and(|v| resolve(v) == eq)
}

fn op_label(op: &Op, _vals: &[Option<Val>]) -> Label {
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
        Op::Recv { sel, blocking } => {
            let pred = match sel {
                Sel::Any => Pred::any(),
                Sel::Eq(s) => Pred::eq(*s),
            };
            if *blocking {
                Label::recv(pred)
            } else {
                Label::recv_nb(pred)
            }
        }
    }
}

fn replay(ops: &[Op], trace: &[Option<Val>]) -> (Vec<Option<Val>>, usize) {
    let mut vals: Vec<Option<Val>> = vec![None; ops.len()];
    let mut cursor = 0;
    for (i, op) in ops.iter().enumerate() {
        let emits = match op {
            Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
            _ => true,
        };
        if !emits {
            continue;
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
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        let ops = &self.threads[tid];
        let (vals, frontier) = replay(ops, trace);
        // Contract (`src/program.rs`): `out[0]` must be *exactly* the thread's next label — the
        // one `next` reports, i.e. `op_label` of the first **emitting** op at/after the frontier
        // (a `SendIf` with a failing guard is skipped by both). Everything from index 1 on
        // over-approximates the ops strictly after it.
        //
        // The head has to come from the same `op_label` call `next` uses, not from the loop
        // below: that loop deliberately emits *several* labels for one op (both windows of an
        // unresolved `SendWin`, every payload of an unresolved `EqGuard`), so it would put the
        // wrong label at index 0. `force_source` condition (3b) does `.skip(1)` on the strength
        // of this, so the mismatch is an over-force, i.e. a completeness loss — pinned by
        // `tests/h1_review.rs::vd_program_violates_the_new_possible_future_head_contract`.
        let Some(head) = (frontier..ops.len()).find(|&i| match &ops[i] {
            Op::SendIf { guard, eq, .. } => guard_hits(&vals, *guard, eq),
            _ => true,
        }) else {
            return Some(Vec::new()); // finished: no future events at all (the exact answer)
        };
        let mut out = vec![op_label(&ops[head], &vals)];
        for op in &ops[head + 1..] {
            match op {
                Op::Nondet => out.push(Label::nondet(["a", "b"])),
                Op::Send { .. } => out.push(op_label(op, &vals)),
                Op::SendIf { guard, eq, .. } => match vals[*guard] {
                    Some(v) if resolve(v) != *eq => {}
                    _ => out.push(op_label(op, &vals)),
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
                    }
                }
            }
        }
        Some(out)
    }
}

// =====================================================================================
// Instrumentation.
// =====================================================================================

/// Instrumentation for the C-B1 mechanism. The load-bearing counter is `dangerous_config`: the
/// number of backward revisits that realize the recipe's dangerous sub-case at their `g_add`
/// (see `is_dangerous`). The blocking invariant predicts it is always 0.
#[derive(Default)]
struct Cb1Probe {
    revisits: AtomicUsize,
    revisits_with_nd_in_deleted: AtomicUsize,
    /// Revisits whose `Deleted` carries a nondet AND a po-later blocking `r''` (the shape's
    /// ingredients present) — coverage that the dangerous *shape* is actually explored.
    revisits_nd_and_rpp: AtomicUsize,
    viable_calls: AtomicUsize,
    viable_false: AtomicUsize,
    /// THE witness: revisits realizing the full dangerous sub-case at `g_add` (`is_dangerous`).
    dangerous_config: AtomicUsize,
    /// SHARPENED coverage: revisits whose `Deleted` carries a nondet `ep` AND a po-later
    /// blocking `r''` with `stamp(r'') ≤ stamp(ep)` — the stamp INVERSION the first proof's
    /// (refuted) lemma claimed was impossible. `> 0` proves it is reachable; the point is that
    /// it never co-occurs with an infeasible `g_add` (the dangerous config still 0).
    inversions: AtomicUsize,
    /// The drain-first feasibility invariant, witnessed: every maximal SEND added onto a
    /// feasible graph (`send_adds`) keeps it eager-feasible — `infeas_send_add` counts the
    /// exceptions. C-B1 needs an infeasible `g_add`; this staying 0 is exactly why it cannot
    /// arise. Measured over ALL send additions (fired/rejected/gate-pruned revisits alike),
    /// via `on_event_added`, so it does not depend on any revisit actually firing.
    send_adds: AtomicUsize,
    infeas_send_add: AtomicUsize,
    log: Mutex<Vec<String>>,
}

/// Whether the backward revisit `(r, s)` on graph `g_add` realizes the C-B1 dangerous sub-case —
/// the exact configuration the blocking invariant forbids, checked with real stamps on the real
/// (pre-`restrict`) graph `g_add`:
///
///   * a nondet `ep ∈ Deleted` (so the revisit deletes it ⇒ value-free `g2`);
///   * a blocking receive `r'' ∈ Deleted`, po-LATER than `r` on `r`'s thread, reading a source
///     `w` — and `stamp(r'') ≤ stamp(ep)`, i.e. `r'' ∈ Previous(ep)` so it is retained in
///     `base = viability_base(g_add, ep, porf_s)` with its old (late) rf; and
///   * `g_add` is eager-time-INFEASIBLE — the "`s` is a violating competitor of `r''`" precondition
///     that the revisit must *heal* (by deleting `r''`) and that makes `viable(min)` come out false.
///
/// If all hold the recipe's uniform-false PASS is live and a duplicate is imminent. SHARPENED
/// finding: the stamp inequality `stamp(r'') ≤ stamp(ep)` (the inversion) IS reachable — the
/// first proof that ruled it out is refuted — but it never co-occurs with the last conjunct, an
/// eager-INFEASIBLE `g_add`, so this still returns `false` on every explored revisit. The reason
/// is the DES drain-first invariant: a maximal newly-added send is never a violating competitor,
/// so `g_add` is always eager-feasible (`infeas_send_add == 0`; see the file header).
fn is_dangerous(g_add: &ExecutionGraph, r: EventId, deleted: &BTreeSet<EventId>) -> bool {
    // A nondet in Deleted.
    let Some(ep) = deleted.iter().copied().find(|&d| g_add.nd_value(d).is_some()) else {
        return false;
    };
    let ep_stamp = g_add.stamp(ep);
    // A po-later blocking r'' in Deleted, on r's thread, reading a source, with stamp ≤ stamp(ep).
    let has_rpp = deleted.iter().any(|&d| {
        d.tid == r.tid
            && d.idx > r.idx
            && g_add.label(d).blocking() == Some(true)
            && g_add.reads_from(d).is_some()
            && g_add.stamp(d) <= ep_stamp
    });
    if !has_rpp {
        return false;
    }
    // g_add eager-infeasible (the healing precondition). `check` assumes Asyn/P2p (the generator's
    // only models) and a consistent graph with no ⊥-reading blocking receive (true for g_add).
    !must::time::check(g_add).is_feasible()
}

impl Observer for Cb1Probe {
    /// The drain-first witness (`infeas_send_add`): every maximal SEND addition is checked for
    /// eager-feasibility of the resulting `g_add`. This is the root precondition of C-B1 —
    /// measured over *all* send additions, independent of whether any revisit fires.
    fn on_event_added(&self, g: &ExecutionGraph, e: EventId) {
        if !g.label(e).is_send() {
            return;
        }
        self.send_adds.fetch_add(1, Relaxed);
        if !must::time::check(g).is_feasible() {
            self.infeas_send_add.fetch_add(1, Relaxed);
            self.log.lock().unwrap().push(format!(
                "!!! INFEASIBLE g_add after maximal send {e} — the C-B1 root precondition; \
                 inspect every candidate revisit here for a nondet in Deleted"
            ));
        }
    }
    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        deleted: &BTreeSet<EventId>,
    ) {
        self.revisits.fetch_add(1, Relaxed);
        let has_nd = deleted.iter().any(|&d| g.nd_value(d).is_some());
        if !has_nd {
            return;
        }
        self.revisits_with_nd_in_deleted.fetch_add(1, Relaxed);
        // Coverage: the dangerous *shape* (nondet + po-later blocking r'' both in Deleted).
        let ep = deleted.iter().copied().find(|&d| g.nd_value(d).is_some());
        let shape = deleted.iter().any(|&d| {
            d.tid == r.tid
                && d.idx > r.idx
                && g.label(d).blocking() == Some(true)
                && g.reads_from(d).is_some()
        });
        if shape {
            self.revisits_nd_and_rpp.fetch_add(1, Relaxed);
        }
        // SHARPENED: the stamp INVERSION (stamp(r'') ≤ stamp(ep)), refuting the old lemma.
        if let Some(ep) = ep {
            let ep_stamp = g.stamp(ep);
            let inv = deleted.iter().any(|&d| {
                d.tid == r.tid
                    && d.idx > r.idx
                    && g.label(d).blocking() == Some(true)
                    && g.reads_from(d).is_some()
                    && g.stamp(d) <= ep_stamp
            });
            if inv {
                self.inversions.fetch_add(1, Relaxed);
            }
        }
        // The faithful witness of the FULL dangerous sub-case.
        if is_dangerous(g, r, deleted) {
            self.dangerous_config.fetch_add(1, Relaxed);
            self.log.lock().unwrap().push(format!(
                "!!! DANGEROUS revisit r={r} s={s}: nondet+po-later-blocking-r'' in Deleted with \
                 stamp(r'')≤stamp(ep) AND g_add eager-infeasible"
            ));
        }
    }
    fn on_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: EventId,
        _v: Val,
        _revisiting: EventId,
        _rev_label: &Label,
        verdict: bool,
    ) {
        self.viable_calls.fetch_add(1, Relaxed);
        if !verdict {
            self.viable_false.fetch_add(1, Relaxed);
        }
    }
}

// =====================================================================================
// Harness: run T1-filter / zombie / T2-predicate; assert completeness & no-dup.
// =====================================================================================

struct Report {
    t1_full: BTreeSet<String>,
    zb_full: BTreeSet<String>,
    t2_full: BTreeSet<String>,
    t2_terms: Vec<String>,
    revisits: usize,
    nd_revisits: usize,
    nd_rpp_revisits: usize,
    inversions: usize,
    send_adds: usize,
    infeas_send_add: usize,
    viable_calls: usize,
    viable_false: usize,
    dangerous: usize,
    log: Vec<String>,
}

impl Report {
    fn dup_keys(&self) -> Vec<String> {
        let mut seen = BTreeSet::new();
        let mut dups = BTreeSet::new();
        for k in &self.t2_terms {
            if !seen.insert(k.clone()) {
                dups.insert(k.clone());
            }
        }
        dups.into_iter().collect()
    }
    fn has_dup(&self) -> bool {
        !self.dup_keys().is_empty()
    }
}

fn run_report<P: Program + Clone + Sync>(prog: &P) -> Report {
    let mk = || prog.clone();

    let t1 = ExecutionCollector::new();
    explore(mk, &t1, Config::default().collect_errors().with_time_filter());
    let t1_full: BTreeSet<String> = t1.full_keys().into_iter().collect();

    let zb = ExecutionCollector::new();
    explore(mk, &zb, Config::default().collect_errors().with_time_zombie());
    let zb_full: BTreeSet<String> = zb.full_keys().into_iter().collect();

    let obs = (ExecutionCollector::new(), Cb1Probe::default());
    explore(
        mk,
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let (col, probe) = obs;

    Report {
        t1_full,
        zb_full,
        t2_full: col.full_keys().into_iter().collect(),
        t2_terms: col.terminal_keys(),
        revisits: probe.revisits.load(Relaxed),
        nd_revisits: probe.revisits_with_nd_in_deleted.load(Relaxed),
        nd_rpp_revisits: probe.revisits_nd_and_rpp.load(Relaxed),
        inversions: probe.inversions.load(Relaxed),
        send_adds: probe.send_adds.load(Relaxed),
        infeas_send_add: probe.infeas_send_add.load(Relaxed),
        viable_calls: probe.viable_calls.load(Relaxed),
        viable_false: probe.viable_false.load(Relaxed),
        dangerous: probe.dangerous_config.load(Relaxed),
        log: probe.log.into_inner().unwrap(),
    }
}

/// Assert the load-bearing invariants (completeness + zombie agreement + no dup) and return
/// whether a duplicate was (unexpectedly) seen.
fn vet<P: Program + Clone + Sync + std::fmt::Debug>(name: &str, prog: &P) -> Report {
    let rep = run_report(prog);
    assert_eq!(
        rep.zb_full, rep.t1_full,
        "{name}: zombie full-set != T1-filter full-set (arbiter broke)"
    );
    assert_eq!(
        rep.t2_full, rep.t1_full,
        "{name}: COMPLETENESS FINDING — T2 realizable full-set != T1-filter full-set.\n  \
         T1\\T2 = {:?}\n  T2\\T1 = {:?}\n  prog={prog:#?}",
        rep.t1_full.difference(&rep.t2_full).collect::<Vec<_>>(),
        rep.t2_full.difference(&rep.t1_full).collect::<Vec<_>>(),
    );
    rep
}

// =====================================================================================
// Directed System build: the recipe scaffold + the 5th ingredient.
// =====================================================================================

/// The recipe scaffold (bug_class_program) extended with a po-late blocking `r''` on the monitor
/// reading a late `w`, with an early-windowed `L`. Illustrates the safe landing: `r''` fires late
/// (reads `w`@50) so it is inserted AFTER the revisiting `L`, never lands in `base`, and
/// `viable("m")` stays true ⇒ no duplicate. (Value-independent nondet, so the runtime System is a
/// valid vehicle; `possible_future=None` uses the C1-safe gate fallback.)
fn scaffold_plus_rpp() -> System {
    let mut sys = System::new();
    sys.add(|c: Ctx| async move {
        c.send_within(0, "t0", Model::Asyn, Window::new(1, 1));
        c.recv(|x: &str| x == "t0").await;
        let m = c.recv(|x: &str| x == "v").await;
        if m == "v" {
            c.send_within(3, "L", Model::Asyn, Window::new(0, 0));
        }
    });
    sys.add(|c: Ctx| async move {
        c.recv(|x: &str| x == "g").await;
        c.send_within(0, "v", Model::Asyn, Window::new(0, 0));
    });
    sys.add(|c: Ctx| async move {
        c.send_within(1, "g", Model::Asyn, Window::new(5, 5));
        c.send_within(2, "q", Model::Asyn, Window::new(2, 2));
        c.recv(|x: &str| x == "q").await;
        c.nondet(["m", "z"]).await;
    });
    sys.add(|c: Ctx| async move {
        c.recv_timeout(|x: &str| x == "L").await;
        c.recv(|x: &str| x == "L" || x == "w").await;
    });
    sys.add(|c: Ctx| async move {
        c.send_within(3, "w", Model::Asyn, Window::new(50, 50));
    });
    sys
}

/// The unmodified scaffold — the known-good min-holder-PASS baseline (no dup).
fn scaffold() -> System {
    let mut sys = System::new();
    sys.add(|c: Ctx| async move {
        c.send_within(0, "t0", Model::Asyn, Window::new(1, 1));
        c.recv(|x: &str| x == "t0").await;
        let m = c.recv(|x: &str| x == "v").await;
        if m == "v" {
            c.send(3, "L", Model::Asyn);
        }
    });
    sys.add(|c: Ctx| async move {
        c.recv(|x: &str| x == "g").await;
        c.send_within(0, "v", Model::Asyn, Window::new(0, 0));
    });
    sys.add(|c: Ctx| async move {
        c.send_within(1, "g", Model::Asyn, Window::new(5, 5));
        c.send_within(2, "q", Model::Asyn, Window::new(2, 2));
        c.recv(|x: &str| x == "q").await;
        c.nondet(["m", "z"]).await;
    });
    sys.add(|c: Ctx| async move {
        c.recv_timeout(|x: &str| x == "L").await;
    });
    sys
}

// =====================================================================================
// Directed VdProgram builds attempting the 2-hop dangerous sub-case explicitly.
// =====================================================================================

const AS: Model = Model::Asyn;

fn send(dst: usize, val: &'static str, lo: u64, hi: u64) -> Op {
    Op::Send {
        dst,
        model: AS,
        val,
        lo,
        hi,
    }
}
fn brecv(sel: Sel) -> Op {
    Op::Recv { sel, blocking: true }
}
fn nbrecv(sel: Sel) -> Op {
    Op::Recv {
        sel,
        blocking: false,
    }
}

/// Directed C-B1 attempt: victim T0 = `nbrecv(=L)`  then a blocking `r''` matching {L, w}; a
/// late `w`@[8,8] to T0; an EARLY `L`@[0,0] revisiting send from a relay whose Occ is pushed up
/// so `L` is nonetheless added late — the (impossible) "early-avail, late-stamp" send. The nondet
/// sits po-after a late blocking recv so it enters `Deleted`. Expected: the forced competitor
/// violation drags `L`'s stamp below `r''`, so either `r''` is absent from `g_add` or `L` is not a
/// violating competitor ⇒ no dup.
fn vd_attempt_2hop() -> VdProgram {
    VdProgram {
        threads: vec![
            // T0 victim: nb-recv(=L) [= r], then blocking r'' matching {L, w}
            vec![nbrecv(Sel::Eq("L")), brecv(Sel::Any)],
            // T1 relay → victim: late "g" pushes Occ up, then EARLY "L"@[0,0] (avail = Occ)
            vec![brecv(Sel::Eq("g")), send(0, "L", 0, 0)],
            // T2 feeds relay late so L's Occ (hence stamp) is large but avail small vs w
            vec![send(1, "g", 1, 1)],
            // T3 ep carrier: late blocking recv, THEN nondet (⇒ nondet enters Deleted late)
            vec![brecv(Sel::Eq("k")), Op::Nondet],
            // T4 feeds the ep carrier's blocking recv late (so the nondet is inserted late)
            vec![send(3, "k", 6, 6)],
            // T5 late "w"@[8,8] to the victim — r'' 's late source
            vec![send(0, "w", 8, 8)],
        ],
    }
}

/// A second directed attempt: victim has an EARLY source for `r''` (so `r''` is woken early with a
/// low stamp) that is consumed by an intervening receive, plus a late `w` — probing whether a
/// prior revisit can hand `r''` a late read at a low stamp. Expected safe (the freed early source
/// becomes a competitor / the late read raises the wake time).
fn vd_attempt_early_source() -> VdProgram {
    VdProgram {
        threads: vec![
            // T0 victim: nb-recv(=L) [=r]; recv(=e) consumes the early source; blocking r''(any)
            vec![nbrecv(Sel::Eq("L")), brecv(Sel::Eq("e")), brecv(Sel::Any)],
            // T1 relay → victim: late g, then early L
            vec![brecv(Sel::Eq("g")), send(0, "L", 0, 0)],
            // T2 feed relay
            vec![send(1, "g", 2, 2)],
            // T3 ep carrier late nondet
            vec![brecv(Sel::Eq("k")), Op::Nondet],
            // T4 feed carrier
            vec![send(3, "k", 5, 5)],
            // T5 early "e" (consumed) + T6 late "w"
            vec![send(0, "e", 0, 0)],
            vec![send(0, "w", 7, 7)],
        ],
    }
}

// =====================================================================================
// C-B1-biased randomized corpus (SplitMix64, no external crate).
// =====================================================================================

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }
    fn u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.u64() % n as u64) as usize
    }
    fn chance(&mut self, pct: usize) -> bool {
        self.below(100) < pct
    }
}

fn rwin(rng: &mut Rng) -> (u64, u64) {
    match rng.below(7) {
        0 => (0, 0),
        1 => (0, 1),
        2 => (1, 1),
        3 => (1, 2),
        4 => (2, 3),
        5 => (4, 5),
        _ => (6, 8),
    }
}

/// Structured C-B1 generator. Fixed skeleton enforcing every ingredient of the dangerous
/// sub-case; windows / models / selectors randomized so the DES stamp order and competitor
/// relations vary widely:
///   * T0 victim: `nbrecv(=L)` [= r, reads ⊥] then a blocking `r''` (the po-later blocking recv)
///     matching a broad predicate so `L` and the late `w` both compete;
///   * T1 relay + T2 feeder: a late chain that emits the revisiting `L` to the victim;
///   * T3 ep-carrier: a (possibly late) blocking recv, THEN the nondet — so the nondet lands in
///     `Deleted`, po-after `r`, outside `porf(L)`;
///   * T4 feeder for the ep-carrier; T5/T6 sends of the late `w` and an extra racer to the victim.
fn gen_cb1(rng: &mut Rng) -> VdProgram {
    let m = |rng: &mut Rng| if rng.chance(50) { Model::Asyn } else { Model::P2p };
    let victim = 0;

    let (glo, ghi) = rwin(rng);
    let (llo, lhi) = if rng.chance(60) { (0, 0) } else { rwin(rng) };
    let (wlo, whi) = {
        // Bias w LATE so it can be r'''s late source.
        let lo = 4 + rng.below(4) as u64;
        (lo, lo + rng.below(2) as u64)
    };
    let (klo, khi) = rwin(rng); // ep-carrier feeder
    let (rlo, rhi) = rwin(rng); // extra racer to victim

    // r'' predicate: broad enough that L and w both match (so both can be competitors).
    let rpp_sel = match rng.below(3) {
        0 => Sel::Any,
        1 => Sel::Eq("w"),
        _ => Sel::Eq("L"),
    };
    let relay_sel = if rng.chance(50) { Sel::Eq("g") } else { Sel::Any };
    let carrier_sel = if rng.chance(50) { Sel::Eq("k") } else { Sel::Any };

    let threads = vec![
        // T0 victim
        vec![nbrecv(Sel::Eq("L")), brecv(rpp_sel)],
        // T1 relay → victim (late L)
        vec![
            Op::Recv {
                sel: relay_sel,
                blocking: true,
            },
            Op::Send {
                dst: victim,
                model: m(rng),
                val: "L",
                lo: llo,
                hi: lhi,
            },
        ],
        // T2 feed relay
        vec![Op::Send {
            dst: 1,
            model: m(rng),
            val: "g",
            lo: glo,
            hi: ghi,
        }],
        // T3 ep carrier: (late) blocking recv, then nondet, and — half the time — a send GATED on
        // the nondet value (making ep value-DEPENDENT). The gated emit exercises the `viable`
        // false path (a smaller value can be non-viable when it withholds the send), broadening the
        // no-dup claim past strictly value-independent nondets.
        {
            let mut ops = vec![
                Op::Recv {
                    sel: carrier_sel,
                    blocking: true,
                },
                Op::Nondet,
            ];
            if rng.chance(50) {
                let (dst, val) = if rng.chance(50) { (victim, "L") } else { (1usize, "g") };
                let (elo, ehi) = rwin(rng);
                ops.push(Op::SendIf {
                    guard: 1, // the nondet op index
                    eq: "a",
                    dst,
                    model: m(rng),
                    val,
                    lo: elo,
                    hi: ehi,
                });
            }
            ops
        },
        // T4 feed the ep carrier
        vec![Op::Send {
            dst: 3,
            model: m(rng),
            val: "k",
            lo: klo,
            hi: khi,
        }],
        // T5 late w to victim
        vec![Op::Send {
            dst: victim,
            model: m(rng),
            val: "w",
            lo: wlo,
            hi: whi,
        }],
        // T6 extra racer to victim
        vec![Op::Send {
            dst: victim,
            model: m(rng),
            val: if rng.chance(50) { "L" } else { "w" },
            lo: rlo,
            hi: rhi,
        }],
    ];
    VdProgram { threads }
}

// =====================================================================================
// SHARPENED corpus: the survivor-inversion generators (the reviewer's 2-hop shape).
//
// The first corpus (`gen_cb1`) never produced the stamp inversion `stamp(r'') ≤ stamp(ep)`.
// These families do: `T0 = [r, r'', s1]` emits `s1` po-after `r''` so `r'' ∈ porf(s1)`, a relay
// victim `r1` lets `s1` revisit, and the nondet is gated behind a blocking receive so it is
// re-added late — the exact ingredients for a survivor `r''` at a stamp below a re-added `ep`.
// They reach the inversion (`inversions > 0`) yet never an infeasible `g_add`
// (`infeas_send_add == 0`), which is the sharpened obstruction.
// =====================================================================================

fn model(rng: &mut Rng) -> Model {
    if rng.chance(70) {
        Model::Asyn
    } else {
        Model::P2p
    }
}

/// A random timed send (model + window from one `rwin` draw, so `lo ≤ hi`).
fn tsnd(rng: &mut Rng, dst: usize, val: &'static str) -> Op {
    let m = model(rng);
    let (lo, hi) = rwin(rng);
    Op::Send { dst, model: m, val, lo, hi }
}

/// `Deleted(r, s)` on `g`: `{x : stamp(x) > stamp(r) ∧ x ∉ porf(s)}` (line 11) — for the
/// hand-built positive control's assertions.
fn deleted_of(g: &ExecutionGraph, r: EventId, s: EventId) -> BTreeSet<EventId> {
    let porf_s = g.porf_prefix(s);
    let sr = g.stamp(r);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) > sr && !porf_s.contains(&x))
        .collect()
}

/// Survivor family A: T0 victim emits `s1` after `r''`; late `w`, early `S`, a gated nondet.
fn gen_survivor_a(rng: &mut Rng) -> VdProgram {
    let broad0 = match rng.below(3) {
        0 => Sel::Any,
        1 => Sel::Eq("w"),
        _ => Sel::Eq("S"),
    };
    let r = if rng.chance(50) { nbrecv(broad0) } else { brecv(broad0) };
    let (wlo, whi) = {
        let lo = 4 + rng.below(6) as u64;
        (lo, lo + rng.below(2) as u64)
    };
    let (slo, shi) = if rng.chance(70) { (0, 0) } else { (0, 1) };
    let extra = if rng.chance(50) { "S" } else { "w" };
    VdProgram {
        threads: vec![
            vec![r, brecv(Sel::Any), Op::Send { dst: 3, model: model(rng), val: "u", lo: 0, hi: 0 }],
            vec![Op::Send { dst: 0, model: model(rng), val: "w", lo: wlo, hi: whi }],
            vec![Op::Send { dst: 0, model: model(rng), val: "S", lo: slo, hi: shi }],
            vec![if rng.chance(60) { brecv(Sel::Eq("u")) } else { nbrecv(Sel::Eq("u")) }],
            vec![brecv(Sel::Eq("k")), Op::Nondet],
            vec![tsnd(rng, 4, "k")],
            vec![Op::Send { dst: 0, model: model(rng), val: extra, lo: 0, hi: 0 }],
        ],
    }
}

/// Survivor family B: the early competitor `S` is itself gated behind a receive (a second
/// route to a late-added early-window send), stressing the occ-vs-avail tension directly.
fn gen_survivor_b(rng: &mut Rng) -> VdProgram {
    let (wlo, whi) = {
        let lo = 4 + rng.below(6) as u64;
        (lo, lo + rng.below(2) as u64)
    };
    VdProgram {
        threads: vec![
            vec![nbrecv(Sel::Any), brecv(Sel::Any), Op::Send { dst: 3, model: model(rng), val: "u", lo: 0, hi: 0 }],
            vec![Op::Send { dst: 0, model: model(rng), val: "w", lo: wlo, hi: whi }],
            vec![brecv(Sel::Eq("g")), Op::Send { dst: 0, model: model(rng), val: "S", lo: 0, hi: 0 }],
            vec![brecv(Sel::Eq("u"))],
            vec![brecv(Sel::Eq("k")), Op::Nondet],
            vec![tsnd(rng, 4, "k")],
            vec![tsnd(rng, 2, "g")],
        ],
    }
}

/// Survivor family C: fully random 6–8 thread timed programs with the T0 victim skeleton and
/// several timed sources to thread 0 — maximal diversity of DES order and revisit structure.
fn gen_survivor_c(rng: &mut Rng) -> VdProgram {
    let nthreads = 6 + rng.below(3);
    let mut threads: Vec<Vec<Op>> = Vec::new();
    let mut t0 = vec![
        if rng.chance(50) { nbrecv(Sel::Any) } else { brecv(Sel::Any) },
        brecv(Sel::Any),
    ];
    if rng.chance(60) {
        let d = 3 + rng.below(nthreads.saturating_sub(3)).max(1);
        t0.push(Op::Send { dst: d, model: model(rng), val: "u", lo: 0, hi: 0 });
    }
    threads.push(t0);
    let vals = ["w", "S", "p", "q"];
    for _ in 1..nthreads {
        let t: Vec<Op> = match rng.below(5) {
            0 => {
                let m = model(rng);
                let v = vals[rng.below(vals.len())];
                let lo = rng.below(12) as u64;
                vec![Op::Send { dst: 0, model: m, val: v, lo, hi: lo + rng.below(2) as u64 }]
            }
            1 => vec![brecv(Sel::Eq("u"))],
            2 => vec![brecv(Sel::Eq("k")), Op::Nondet],
            3 => {
                let d = 1 + rng.below(nthreads - 1);
                vec![tsnd(rng, d, "k")]
            }
            _ => {
                let v = vals[rng.below(vals.len())];
                vec![Op::Send { dst: 0, model: model(rng), val: v, lo: 0, hi: 0 }]
            }
        };
        threads.push(t);
    }
    VdProgram { threads }
}

/// The C-B1 *mechanism* is live: on the exact `g_add` the recipe wants (infeasible — `r''←w`
/// late, `S` early-unread competitor — with a nondet `ep ∈ Deleted`), [`must::time::viable`] is
/// uniform-FALSE over every nondet value, so the min-holder passes trivially AND every non-min
/// holder passes ⇒ two branches emit the same `ep`-free `g2` ⇒ a DUPLICATE. This proves the
/// oracle is not immune to the bug; the corpus proves the *state* is forward-unreachable.
#[test]
fn cb1_mechanism_positive_control() {
    // The program the base/g_add are prefixes of.
    let prog = VdProgram {
        threads: vec![
            vec![nbrecv(Sel::Any), brecv(Sel::Any)], // T0: r (⊥), r'' (←w)
            vec![send(0, "w", 50, 50)],              // T1: late w
            vec![Op::Nondet],                        // T2: ep
            vec![send(0, "S", 0, 0)],                // T3: early S (the revisiting send)
        ],
    };

    // g_add = the full forward graph + S: r reads ⊥, r''←w, S unread.
    let mut g = ExecutionGraph::new();
    let r = g.add_event(0, Label::recv_nb(Pred::any()));
    let rpp = g.add_event(0, Label::recv(Pred::any()));
    let w = g.add_event(1, Label::send_within(Model::Asyn, 0, "w", Window::new(50, 50)));
    let ep = g.add_event(2, Label::nondet(["a", "b"]));
    g.set_nd(ep, "a".into());
    let s = g.add_event(3, Label::send_within(Model::Asyn, 0, "S", Window::new(0, 0)));
    g.set_rf(r, None);
    g.set_rf(rpp, Some(w));

    assert!(must::consistent(&g), "g_add is untimed-consistent");
    assert!(
        !must::time::check(&g).is_feasible(),
        "the C-B1 g_add IS eager-infeasible (early S beats the late r''←w)"
    );
    let del = deleted_of(&g, r, s);
    assert!(del.contains(&ep), "nondet ep ∈ Deleted(r, S)");
    assert!(del.contains(&rpp), "r'' ∈ Deleted(r, S)");
    assert!(g.stamp(rpp) <= g.stamp(ep), "the stamp inversion holds here by construction");

    // `base` = what `viable` searches: g_add minus S (re-added during the search), r''←w baked
    // in — exactly viability_base's content for this shape (r'' survives into Previous(ep)).
    let mut base = ExecutionGraph::new();
    let br = base.add_event(0, Label::recv_nb(Pred::any()));
    let brpp = base.add_event(0, Label::recv(Pred::any()));
    let bw = base.add_event(1, Label::send_within(Model::Asyn, 0, "w", Window::new(50, 50)));
    let bep = base.add_event(2, Label::nondet(["a", "b"]));
    base.set_rf(br, None);
    base.set_rf(brpp, Some(bw));
    base.set_nd(bep, "a".into());
    assert!(must::consistent(&base));
    assert!(
        must::time::check(&base).is_feasible(),
        "base itself is feasible (no S competitor yet)"
    );

    let s_label = Label::send_within(Model::Asyn, 0, "S", Window::new(0, 0));
    let prio: Vec<usize> = (0..4).collect();
    let mut memo = must::time::ViableMemo::new();
    let va = must::time::viable(&base, bep, "a".into(), &prog, &prio, s, &s_label, &mut memo);
    let vb = must::time::viable(&base, bep, "b".into(), &prog, &prio, s, &s_label, &mut memo);
    assert!(!va, "viable(ep=a) must be FALSE (every completion re-adds S ⇒ infeasible)");
    assert!(!vb, "viable(ep=b) must be FALSE (value-independent)");
    // Both nondet values non-viable ⇒ min-holder "a" PASSes (0 calls) AND non-min "b" PASSes
    // (no smaller value viable) ⇒ the revisit fires from both ⇒ the same g2 is visited twice.
    // The bug is only forward-unreachable, not logically excluded.

    // Sanity: on the FEASIBLE analogue (early w), viable is TRUE, so the non-min holder is
    // correctly rejected — the behaviour on every forward-reachable g_add.
    let prog_ok = VdProgram {
        threads: vec![
            vec![nbrecv(Sel::Any), brecv(Sel::Any)],
            vec![send(0, "w", 0, 0)], // early w now
            vec![Op::Nondet],
            vec![send(0, "S", 0, 0)],
        ],
    };
    let mut base_ok = ExecutionGraph::new();
    let or = base_ok.add_event(0, Label::recv_nb(Pred::any()));
    let orpp = base_ok.add_event(0, Label::recv(Pred::any()));
    let ow = base_ok.add_event(1, Label::send_within(Model::Asyn, 0, "w", Window::new(0, 0)));
    let oep = base_ok.add_event(2, Label::nondet(["a", "b"]));
    base_ok.set_rf(or, None);
    base_ok.set_rf(orpp, Some(ow));
    base_ok.set_nd(oep, "a".into());
    let mut memo2 = must::time::ViableMemo::new();
    let va_ok = must::time::viable(&base_ok, oep, "a".into(), &prog_ok, &prio, s, &s_label, &mut memo2);
    assert!(va_ok, "on a feasible g_add, viable(min) is TRUE ⇒ the non-min holder is rejected");
}

// =====================================================================================
// The machine-verification test.
// =====================================================================================

#[test]
fn cb1_machine_verification() {
    let mut hits: Vec<(String, Vec<String>)> = Vec::new();
    let mut total_revisits = 0usize;
    let mut total_nd_revisits = 0usize;
    let mut total_nd_rpp = 0usize;
    let mut total_viable = 0usize;
    let mut total_false = 0usize;
    let mut total_dangerous = 0usize;
    let mut progs_with_revisit = 0usize;
    let mut progs_with_viable = 0usize;
    let mut progs_with_false = 0usize;

    let mut record = |name: &str, rep: &Report| {
        total_revisits += rep.revisits;
        total_nd_revisits += rep.nd_revisits;
        total_nd_rpp += rep.nd_rpp_revisits;
        total_viable += rep.viable_calls;
        total_false += rep.viable_false;
        total_dangerous += rep.dangerous;
        progs_with_revisit += usize::from(rep.revisits > 0);
        progs_with_viable += usize::from(rep.viable_calls > 0);
        progs_with_false += usize::from(rep.viable_false > 0);
        if rep.has_dup() {
            println!("  !!! [{name}] T2 DUPLICATE: {:#?}", rep.dup_keys());
            for l in &rep.log {
                println!("      {l}");
            }
            hits.push((name.to_string(), rep.dup_keys()));
        }
        if rep.dangerous > 0 {
            println!("  [{name}] DANGEROUS-config count = {}", rep.dangerous);
            for l in &rep.log {
                println!("      {l}");
            }
        }
    };

    // -- Directed System builds (the recipe scaffold + 5th ingredient). --
    for (name, sys) in [
        ("scaffold", scaffold as fn() -> System),
        ("scaffold_plus_rpp", scaffold_plus_rpp as fn() -> System),
    ] {
        // Systems are !Send / not Clone-able as a value; run through fn-pointer builders.
        let t1 = ExecutionCollector::new();
        explore(sys, &t1, Config::default().collect_errors().with_time_filter());
        let t1_full: BTreeSet<String> = t1.full_keys().into_iter().collect();
        let zb = ExecutionCollector::new();
        explore(sys, &zb, Config::default().collect_errors().with_time_zombie());
        let zb_full: BTreeSet<String> = zb.full_keys().into_iter().collect();
        let obs = (ExecutionCollector::new(), Cb1Probe::default());
        explore(sys, &obs, Config::default().collect_errors().with_time_predicate());
        let (col, probe) = obs;
        let rep = Report {
            t1_full: t1_full.clone(),
            zb_full,
            t2_full: col.full_keys().into_iter().collect(),
            t2_terms: col.terminal_keys(),
            revisits: probe.revisits.load(Relaxed),
            nd_revisits: probe.revisits_with_nd_in_deleted.load(Relaxed),
            nd_rpp_revisits: probe.revisits_nd_and_rpp.load(Relaxed),
            inversions: probe.inversions.load(Relaxed),
            send_adds: probe.send_adds.load(Relaxed),
            infeas_send_add: probe.infeas_send_add.load(Relaxed),
            viable_calls: probe.viable_calls.load(Relaxed),
            viable_false: probe.viable_false.load(Relaxed),
            dangerous: probe.dangerous_config.load(Relaxed),
            log: probe.log.into_inner().unwrap(),
        };
        assert_eq!(rep.zb_full, rep.t1_full, "{name}: zombie != T1");
        assert_eq!(rep.t2_full, rep.t1_full, "{name}: COMPLETENESS FINDING (System build)");
        record(name, &rep);
    }

    // -- Directed VdProgram builds. --
    for (name, prog) in [
        ("vd_attempt_2hop", vd_attempt_2hop()),
        ("vd_attempt_early_source", vd_attempt_early_source()),
    ] {
        let rep = vet(name, &prog);
        record(name, &rep);
    }

    // -- Randomized C-B1-biased corpus. --
    let n_progs = if cfg!(debug_assertions) { 1200 } else { 5000 };
    let mut rng = Rng::new(0xCB1_5EED_2026);
    for case in 0..n_progs {
        let prog = gen_cb1(&mut rng);
        let rep = vet(&format!("gen#{case}"), &prog);
        record(&format!("gen#{case}"), &rep);
    }

    println!(
        "C-B1 corpus: {n_progs} random + 4 directed | revisits={total_revisits} \
         nd_in_Deleted_revisits={total_nd_revisits} nd+po-later-r''_revisits={total_nd_rpp} \
         viable_calls={total_viable} viable_false={total_false} dangerous={total_dangerous}"
    );
    println!(
        "  programs: with_revisit={progs_with_revisit} with_viable={progs_with_viable} \
         with_viable_false={progs_with_false} | DUPLICATES={}",
        hits.len()
    );

    // Non-degeneracy floors: the corpus must actually drive the mechanism, else "no dup" is vacuous.
    assert!(
        progs_with_revisit >= n_progs / 5,
        "C-B1 corpus too weak: only {progs_with_revisit}/{n_progs} programs did any backward revisit",
    );
    assert!(
        total_nd_revisits >= 1,
        "C-B1 corpus too weak: not one revisit had a nondet in Deleted (the whole mechanism)",
    );
    assert!(
        total_nd_rpp >= 1,
        "C-B1 corpus too weak: the dangerous SHAPE (nondet + po-later blocking r'' both in \
         Deleted) never even arose — the obstruction result would be vacuous",
    );
    assert!(
        progs_with_viable >= 10,
        "C-B1 corpus too weak: the non-min PASS oracle fired on only {progs_with_viable} programs",
    );
    assert!(
        total_false >= 1,
        "C-B1 corpus too weak: `viable` never returned false, so the load-bearing FALSE path of the \
         PASS oracle (the one that would let a non-min holder wrongly PASS) is untested",
    );

    // The empirical face of the blocking invariant: the FULL dangerous sub-case at `g_add`
    // (a nondet + a po-later blocking r'' in Deleted with stamp(r'') ≤ stamp(ep), and g_add
    // eager-infeasible so the revisit must heal it) is NEVER produced by the DES insertion order —
    // exactly the LB contradiction of the header proof, witnessed on the real graphs.
    assert_eq!(
        total_dangerous, 0,
        "C-B1: the dangerous sub-case configuration arose at some g_add — the recipe's uniform-false \
         PASS is LIVE; investigate for a genuine duplicate",
    );

    // The verdict. A hit here (a T2 duplicate that T1/zombie do not produce, completeness intact)
    // would be REPRODUCED; none occurs ⇒ NO-REPRO.
    assert!(
        hits.is_empty(),
        "C-B1 REPRODUCED: {} program(s) produced a T2 duplicate canonical key. Details above.\n{hits:#?}",
        hits.len(),
    );
}

// =====================================================================================
// SHARPENED verification: the survivor-inversion corpus (the reviewer's 2-hop shape).
// =====================================================================================

/// Build the exact 2-hop survivor shape and hunt for the C-B1 duplicate in it. Unlike
/// `cb1_machine_verification` (whose corpus never reaches the stamp inversion), this corpus
/// DOES reach `stamp(r'') ≤ stamp(ep)` with a low-LB `ep` — refuting the first NO-REPRO's
/// stamp-monotonicity lemma — and still finds no duplicate, because the deeper drain-first
/// invariant keeps `g_add` eager-feasible (`infeas_send_add == 0`).
#[test]
fn cb1_survivor_inversion_no_dup() {
    let n_progs = if cfg!(debug_assertions) { 3000 } else { 16000 };
    let mut rng = Rng::new(0x5A11_7ED0_2026);

    let mut dups: Vec<(usize, Vec<String>)> = Vec::new();
    let mut tot_rev = 0usize;
    let mut tot_nd = 0usize;
    let mut tot_shape = 0usize;
    let mut tot_inv = 0usize;
    let mut tot_send_adds = 0usize;
    let mut tot_infeas = 0usize;
    let mut tot_dang = 0usize;
    let mut infeas_log: Vec<String> = Vec::new();

    let gens: [fn(&mut Rng) -> VdProgram; 3] = [gen_survivor_a, gen_survivor_b, gen_survivor_c];
    for case in 0..n_progs {
        let prog = gens[case % 3](&mut rng);
        let rep = vet(&format!("survivor#{case}"), &prog); // asserts completeness + zombie==T1
        tot_rev += rep.revisits;
        tot_nd += rep.nd_revisits;
        tot_shape += rep.nd_rpp_revisits;
        tot_inv += rep.inversions;
        tot_send_adds += rep.send_adds;
        tot_infeas += rep.infeas_send_add;
        tot_dang += rep.dangerous;
        if rep.has_dup() {
            dups.push((case, rep.dup_keys()));
        }
        if rep.infeas_send_add > 0 {
            infeas_log.extend(rep.log.iter().cloned());
        }
    }

    println!(
        "survivor corpus: {n_progs} programs | revisits={tot_rev} nd_in_Deleted={tot_nd} \
         shape={tot_shape} INVERSIONS={tot_inv} dangerous={tot_dang}"
    );
    println!(
        "  send_adds={tot_send_adds} infeas_send_add={tot_infeas} (0 = drain-first: a maximal \
         send never breaks eager-feasibility) | DUPLICATES={}",
        dups.len()
    );
    for l in &infeas_log {
        println!("  {l}");
    }

    // Non-degeneracy: the corpus must actually build the sharpened shape, else the result is
    // vacuous. The stamp INVERSION `stamp(r'') ≤ stamp(ep)` — the first proof said impossible —
    // must arise, and the nondet-in-Deleted revisit must be exercised.
    assert!(
        tot_nd >= 1,
        "survivor corpus too weak: no revisit had a nondet in Deleted"
    );
    assert!(
        tot_inv >= 1,
        "survivor corpus too weak: the stamp INVERSION (stamp(r'') ≤ stamp(ep)) never arose — \
         the sharpened shape is not being built, so the no-repro is vacuous"
    );

    // The sharpened obstruction, witnessed on the real forward graphs: adding a maximal send to
    // a feasible graph never yields an eager-infeasible `g_add` (drain-first / L-DES-1). Since
    // C-B1 needs an infeasible `g_add`, its root precondition never materialises.
    assert_eq!(
        tot_infeas, 0,
        "C-B1 ROOT PRECONDITION HIT: a maximal send produced an eager-infeasible g_add — the \
         drain-first invariant broke; inspect for a genuine duplicate"
    );
    assert_eq!(
        tot_dang, 0,
        "C-B1: the dangerous sub-case (inversion + infeasible g_add) arose — investigate"
    );

    // The verdict: no T2 duplicate, completeness intact (asserted per-program in `vet`).
    assert!(
        dups.is_empty(),
        "C-B1 REPRODUCED via the survivor-inversion corpus: {} program(s) duplicated. {dups:#?}",
        dups.len()
    );
}
