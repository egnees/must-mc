//! γ4 (risk R5) — machine verification of an optimality-(a) DUPLICATE candidate for the T2
//! eager-time-predicate canon (`T2_PROOFS_B.md` §B1.f-2).
//!
//! # The mechanism under test
//!
//! The nondet PASS rule (`src/explorer/revisit.rs`, `Label::Nondet` arm of `revisit_condition`)
//! passes a holder `v_held` iff **no strictly-smaller value `v` is `viable(base, ep, v, …)`**,
//! where `base = viability_base(g, ep, porf_s)` = `Previous(ep) \ cone(ep)`. The optimality-(a)
//! dedup argument (`B1.b`) assumes two sibling branches that could each host the *same* final
//! revisit `(r_final, s_final)` share the **same `base` content** (holder-independence, O1). γ4
//! asks: if, between a nondet fork and the final revisit, the two value-branches execute
//! **different intermediate revisits** that delete **different pre-fork events** (events in
//! `Previous(ep)` but not in the final `kept` set, i.e. with `stamp(r_final) < stamp(·) ≤
//! stamp(ep)`), then `base¹ ≠ base²` as content, `viable(base², v₁)` answers about the *wrong*
//! base, and both branches can PASS ⇒ the same `g2` is visited twice ⇒ **duplicate**.
//!
//! # What counts (from the task)
//!
//! REPRODUCED ⇔ under `.with_time_predicate()` the terminal keys carry a duplicate canonical key
//! that neither `.with_time_filter()` (T1) nor `.with_time_zombie()` produce, **while T2's dedup'd
//! realizable `full_keys` set still equals the T1 set** (a duplicate, not a completeness loss).
//! A T2-vs-T1 `full_keys` divergence would be a *completeness* finding — reported separately and
//! never silently accepted.
//!
//! The vehicle is the exact-`possible_future` value-dependent table program `VdProgram` (copied
//! from `tests/fuzz_value_dependent.rs`), because an exact future makes `gate_feasible`/`viable`
//! exact — the regime in which the B1.b holder-independence argument (and hence its γ4 breakage)
//! is stated. Directed hand-built shapes plus two γ4-biased randomized generators drive it (one
//! that gates divergent intermediate revisits, one that eagerly *suppresses* the revisiting send
//! so the `viable` oracle actually returns `false` — the verdict a γ4 duplicate needs).
//!
//! # RESULT: NO-REPRO — γ4 does not reproduce; blocked by re-derivability.
//!
//! Across 12004+ directed/randomized value-dependent programs (release), with the oracle forced
//! false 6000× and the SAME oracle question posed against ≥2 *distinct* `base` graphs on 794 of
//! them (the exact γ4 setting), the `viable` verdict was **never** base-content-dependent and no
//! duplicate canonical key ever appeared, while T2's realizable `full_keys` always equalled the
//! T1-filter set (completeness intact).
//!
//! **Blocking invariant (the B1.f-2 candidate, empirically confirmed):** `Previous(ep) \ kept` is
//! *forward-re-derivable*, so the `viable` verdict is a pure function of the **ep-independent
//! forward-closure of `base`**, not of `base`'s raw content. Divergent intermediate revisits can
//! make `base¹ ≠ base²` as content, but the difference is always either (i) ep-*dependent* — hence
//! inside `cone(ep)`, dropped from BOTH bases by `viability_base`; or (ii) ep-*independent* pre-fork
//! content deleted by an ep-caused intermediate revisit — hence a po-suffix-closed hole that
//! `viable`'s forward-completion search (drain + branch from the frontier) simply re-emits. Either
//! way `viable(base¹, v) == viable(base², v)`, so B1.b's holder-independence of the *verdict*
//! survives even though the raw bases differ ⇒ no double PASS ⇒ no γ4 duplicate. This is the
//! machine-checked witness of "`Previous(ep,s)\kept` is uniquely re-derivable from `g2` + program".
//!
//! (A named non-reproduction is a valid result — `t2-next-verify-cb1-gamma4` memo.)
//!
//! # v2 — the SHARPENED recipe (a differently-deleted send BEHIND A CHOICE POINT): still NO-REPRO
//!
//! An adversarial review found the v1 re-derivability argument leaves a *plausible* gap: it holds
//! only when each differing pre-fork event is a **forced** po-suffix hole the drain re-emits
//! identically; it was conjectured to LEAK when a differently-deleted pre-fork **send sits behind a
//! choice point** (a multi-value nondet or a blocking receive) on its thread, because
//! `viable_search`'s step-1 drain only drains *forced* events (send / error / SINGLETON nondet) and
//! PARKS at a multi-value nondet or a blocking receive. A parked send is then re-derivable-either-way
//! in a base that deleted it (Leak 1) but permanent in a base that has it resolved-present (Leak 2),
//! so two sibling bases were hoped to disagree. `gamma4_leak_hunt` builds exactly that shape (racers
//! PARKED behind their own 2-value nondets, some aimed at the MONITOR as competitors of the final
//! revisit; plus the eager-suppression FALSE path crossed with an ep-independent parked competitor
//! to the relay). Result across **40 002** programs (release): `with_viable_false = 20 000`,
//! `with_multi_base = 32 848`, **`with_base_dependent = 0`**, DUPLICATES = 0, and T2 `full_keys` ==
//! T1 `full_keys` on every one (completeness intact). The park changes nothing.
//!
//! Why (the residual invariant, now a two-horn argument the cone + hosting-feasibility close):
//! `viable` is only ever called while a branch is HOSTING the final revisit — its `g2` already
//! passed the T-GATE, so `g2` (and the pre-`restrict` hosting graph `g` it came from) is
//! eager-feasible. A base-dependence flip needs one base whose present-unread pre-fork event `D`
//! forces the tested value's verdict to FALSE while a sibling base lacking `D` answers TRUE. Split
//! on whether `D`'s FALSE-forcing (a time block / an inconsistency) is ep-dependent. Horn 1,
//! ep-INDEPENDENT: `D` present-unread would make the hosting graph `g` itself infeasible (same
//! content, same ep-independent timing), so `g` could never host and that base never arises —
//! presence is permanent (the forward search cannot delete `D`), but a feasible hosting graph
//! proves a present `D` is harmless. Horn 2, ep-DEPENDENT: the receive `D` competes with (or the
//! clock `Occ` that receive rides) depends on `ep`'s value, so it lies in `cone(ep)`, so
//! `viability_base` drops it (and its po-suffix, inclusively) from BOTH bases, so in the base `D`
//! competes with nothing and there is no FALSE. Leak 1's source-absence is independently
//! re-derivable: the DFS branches every (thread × option) and drains forced sends to quiescence
//! before committing any receive, so a parked source is re-forked and re-emitted in some completion
//! — absence is never permanent. Both horns and Leak 1 are machine-confirmed by
//! `with_base_dependent == 0` over 40 002 choice-point-behind-send programs, on top of the 12 004 of
//! `gamma4_machine_verification`. The B1.f-2 re-derivability invariant holds.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use must::event::{EventId, Label, Model, Pred, Window};
use must::graph::ExecutionGraph;
use must::intern::resolve;
use must::{
    explore, Config, DeadBranchDetector, ExecutionCollector, Observer, Program, ThreadNext, Val,
};

// =====================================================================================
// Value-dependent table program (exact `possible_future`) — copied from
// tests/fuzz_value_dependent.rs so this file is self-contained.
// =====================================================================================

/// A receive's selectivity: static, or keyed by an earlier value-producing op of the SAME thread.
#[derive(Clone, Copy, Debug)]
enum Sel {
    Any,
    Eq(&'static str),
    /// `Pred::eq(value_of(op[k]))`; a ⊥ read yields a never-matching predicate.
    EqGuard(usize),
}

/// One straight-line op of a thread. Guards reference a po-earlier value-producing op.
#[derive(Clone, Debug)]
enum Op {
    /// `nd{a, b}`.
    Nondet,
    Send {
        dst: usize,
        model: Model,
        val: &'static str,
        lo: u64,
        hi: u64,
    },
    /// Emitted only when `value_of(op[guard]) == eq` — the emit/no-emit axis.
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
        Op::Recv { sel, blocking } => {
            let pred = match sel {
                Sel::Any => Pred::any(),
                Sel::Eq(s) => Pred::eq(*s),
                Sel::EqGuard(k) => match vals[*k] {
                    Some(v) => Pred::eq(resolve(v)),
                    None => Pred::eq("__none__"),
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

/// Replay one thread against its trace: resolved per-op values and the frontier op index.
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
                        Sel::EqGuard(k) => match vals[*k] {
                            Some(v) => out.push(mk(Pred::eq(resolve(v)))),
                            None => {
                                for p in ["a", "b", "g", "L", "x", "__none__"] {
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

// =====================================================================================
// Recording observers: backward revisits and viable verdicts.
// =====================================================================================

#[derive(Default)]
struct RevisitRec {
    /// (r, s, deleted) of every executed backward revisit.
    revisits: Mutex<Vec<(EventId, EventId, Vec<EventId>)>>,
}
impl Observer for RevisitRec {
    fn on_backward_revisit(
        &self,
        _g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        deleted: &BTreeSet<EventId>,
    ) {
        self.revisits
            .lock()
            .unwrap()
            .push((r, s, deleted.iter().copied().collect()));
    }
}

/// One recorded oracle call: `(base canonical key, ep, resolved v, revisiting send, verdict)`.
type ViableCall = (String, EventId, String, EventId, bool);

#[derive(Default)]
struct ViableRec {
    calls: Mutex<Vec<ViableCall>>,
}
impl Observer for ViableRec {
    fn on_viable_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        v: Val,
        revisiting: EventId,
        _rev_label: &Label,
        verdict: bool,
    ) {
        self.calls.lock().unwrap().push((
            base.canonical_key(),
            ep,
            resolve(v).to_string(),
            revisiting,
            verdict,
        ));
    }
}

// =====================================================================================
// Harness: run one program under T1-filter / zombie / T2-predicate, diff the sets.
// =====================================================================================

/// A single canonical oracle *question*: `(revisiting send s, nondet position ep, tested value v)`.
/// The γ4 hypothesis is that the same question, evaluated against two different `base` graphs, can
/// disagree; grouping the recorded verdicts by this key is how we test that directly.
type Question = (EventId, EventId, String);

struct Report {
    t1_full: BTreeSet<String>,
    zb_full: BTreeSet<String>,
    t2_full: BTreeSet<String>,
    /// T2 terminal keys WITH multiplicity (full+blocked).
    t2_terms: Vec<String>,
    dead: usize,
    /// (r,s,deleted) log of the T2 run's backward revisits.
    revisits: Vec<(EventId, EventId, Vec<EventId>)>,
    /// viable-oracle calls of the T2 run.
    viable_calls: Vec<ViableCall>,
}

impl Report {
    /// A duplicate canonical key among T2 terminals (the optimality-(a) violation).
    fn t2_has_dup(&self) -> bool {
        let set: BTreeSet<&String> = self.t2_terms.iter().collect();
        set.len() != self.t2_terms.len()
    }
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
    /// T2's dedup'd realizable set equals the T1-filter reference (completeness intact).
    fn complete(&self) -> bool {
        self.t2_full == self.t1_full
    }
    fn zombie_ok(&self) -> bool {
        self.zb_full == self.t1_full
    }

    /// The DIRECT γ4 danger signal (holder-independence of the *verdict*, which B1.b assumes and
    /// γ4 attacks): the SAME oracle question — same revisiting send `s`, same nondet position `ep`,
    /// same tested value `v` — evaluated against ≥ 2 DIFFERENT `base` graphs that disagree on the
    /// verdict. If this never fires, the verdict is empirically base-content-independent, i.e. the
    /// "Previous(ep,s)\kept is re-derivable" invariant holds ⇒ γ4 cannot manufacture a duplicate.
    /// Returns the offending `(s, ep, v)` questions, each with the set of distinct base keys seen.
    fn base_dependent_verdicts(&self) -> Vec<Question> {
        // question (s, ep, v) -> (verdicts seen, distinct base keys)
        let mut groups: BTreeMap<Question, (BTreeSet<bool>, BTreeSet<String>)> = BTreeMap::new();
        for (base_key, ep, v, s, verdict) in &self.viable_calls {
            let g = groups.entry((*s, *ep, v.clone())).or_default();
            g.0.insert(*verdict);
            g.1.insert(base_key.clone());
        }
        groups
            .into_iter()
            .filter(|(_, (verdicts, bases))| verdicts.len() > 1 && bases.len() > 1)
            .map(|((s, ep, v), _)| (s, ep, v))
            .collect()
    }

    /// Whether any oracle question was posed against ≥ 2 distinct bases at all (the *precondition*
    /// of γ4: divergent bases for the same question). Coverage signal — if this is 0 the corpus
    /// never even created the setting γ4 needs.
    fn multi_base_questions(&self) -> usize {
        let mut groups: BTreeMap<Question, BTreeSet<String>> = BTreeMap::new();
        for (base_key, ep, v, s, _verdict) in &self.viable_calls {
            groups
                .entry((*s, *ep, v.clone()))
                .or_default()
                .insert(base_key.clone());
        }
        groups.values().filter(|bases| bases.len() > 1).count()
    }
}

fn run_all(prog: &VdProgram) -> Report {
    // T1-filter reference.
    let t1 = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &t1,
        Config::default().collect_errors().with_time_filter(),
    );
    let t1_full: BTreeSet<String> = t1.full_keys().into_iter().collect();

    // Zombie arbiter.
    let zb = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &zb,
        Config::default().collect_errors().with_time_zombie(),
    );
    let zb_full: BTreeSet<String> = zb.full_keys().into_iter().collect();

    // T2 predicate + full instrumentation.
    let obs = (
        ExecutionCollector::new(),
        (
            DeadBranchDetector::new(),
            (RevisitRec::default(), ViableRec::default()),
        ),
    );
    explore(
        || prog.clone(),
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let (col, (dead, (rev, viable))) = obs;

    Report {
        t1_full,
        zb_full,
        t2_full: col.full_keys().into_iter().collect(),
        t2_terms: col.terminal_keys(),
        dead: dead.dead(),
        revisits: rev.revisits.into_inner().unwrap(),
        viable_calls: viable.calls.into_inner().unwrap(),
    }
}

// =====================================================================================
// Program builders.
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
fn send_if(guard: usize, eq: &'static str, dst: usize, val: &'static str, lo: u64, hi: u64) -> Op {
    Op::SendIf {
        guard,
        eq,
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

/// Directed γ4 attempt #1. Idea:
///  * T0 (monitor / victim): a non-blocking `recv(=L)` — the final revisit target. Reads ⊥ or
///    "L" (via a backward revisit by T1's late "L").
///  * T1 (relay → monitor): `recv(=x); send(0,"L",[0,∞))` — a late "L" (po-after a receive
///    that fires only when "x" is delivered), which backward-revisits the monitor.
///  * T2 (feed relay): `send(1,"x")`.
///  * T3 (ep carrier + gated relay): `recv(=q); nd{a,b}; SendIf(nd=="a" → send(4,"L2",late))` —
///    the nondet gates a SECOND late send that, only in the "a" branch, backward-revisits T4's
///    receive, deleting a pre-fork racing send present in the "b" branch. The nondet sits
///    po-after `recv(=q)`, so it enters late and lands in the monitor-revisit's `Deleted`.
///  * T4 (second monitor / intermediate victim): two receives racing several sources.
///  * feeders drive `q` and the racing sends with near-tie windows.
fn attempt1() -> VdProgram {
    VdProgram {
        threads: vec![
            // T0 monitor
            vec![nbrecv(Sel::Eq("L"))],
            // T1 relay → monitor: late L
            vec![brecv(Sel::Eq("x")), send(0, "L", 0, 0)],
            // T2 feed relay
            vec![send(1, "x", 0, 1)],
            // T3 ep carrier + gated relay
            vec![
                brecv(Sel::Eq("q")),
                Op::Nondet,
                send_if(1, "a", 4, "y", 0, 0),
            ],
            // T4 intermediate victim: races y (gated) against an early racer
            vec![send(3, "q", 2, 2), brecv(Sel::Any)],
            // T5 racer to T4 (pre-fork)
            vec![send(4, "r", 1, 1)],
        ],
    }
}

/// Directed γ4 attempt #2 — closer to the recipe: TWO relays feeding one shared intermediate
/// victim, with the nondet selecting *which* relay's late send wins the intermediate revisit, so
/// each branch deletes a different pre-fork send from `Previous(ep)`.
fn attempt2() -> VdProgram {
    VdProgram {
        threads: vec![
            // T0 monitor (final revisit target)
            vec![nbrecv(Sel::Eq("L"))],
            // T1 relay producing the FINAL late "L" to the monitor
            vec![brecv(Sel::Eq("g")), send(0, "L", 0, 0)],
            // T2 feeds relay T1 (drives "g" late so "L" is late)
            vec![send(1, "g", 3, 3)],
            // T3 ep carrier: recv(=q); nd; then two guarded late relays into the shared victim T4
            vec![
                brecv(Sel::Eq("q")),
                Op::Nondet,
                send_if(1, "a", 4, "u", 0, 0), // only if nd=="a"
                send_if(1, "b", 4, "w", 0, 0), // only if nd=="b"  (mutually exclusive)
            ],
            // T4 shared intermediate victim: recv(any) — revisited by u (a-branch) or w (b-branch)
            vec![send(3, "q", 1, 1), brecv(Sel::Any)],
            // T5, T6 pre-fork racers into T4 (different ones deleted per branch)
            vec![send(4, "p", 0, 1)],
            vec![send(4, "r", 0, 1)],
        ],
    }
}

/// Directed γ4 attempt #3: the ep nondet's value gates whether an *early competitor* to the
/// intermediate victim's read exists, flipping which pre-fork send is consumed vs. deleted.
fn attempt3() -> VdProgram {
    VdProgram {
        threads: vec![
            // T0 monitor
            vec![nbrecv(Sel::Eq("L"))],
            // T1 final relay → monitor
            vec![brecv(Sel::Eq("g")), send(0, "L", 0, 0)],
            // T2 feed final relay (late)
            vec![send(1, "g", 4, 4)],
            // T3 ep carrier: recv(=q); nd; SendIf(a → extra competitor into T4)
            vec![
                brecv(Sel::Eq("q")),
                Op::Nondet,
                send_if(1, "a", 4, "c", 0, 0),
            ],
            // T4 intermediate victim with two receives (consumed-competitor shape)
            vec![send(3, "q", 1, 1), brecv(Sel::Any), brecv(Sel::Any)],
            // T5 late relay into T4 (the intermediate revisiting send)
            vec![brecv(Sel::Eq("z")), send(4, "m", 0, 0)],
            // T6 feed T5 late; T7 pre-fork racer into T4
            vec![send(5, "z", 3, 3)],
            vec![send(4, "d", 0, 1)],
        ],
    }
}

/// Directed γ4 attempt #4 — the theoretically-riskiest shape: the ep-gated intermediate revisit
/// deletes a *receive with an established read* of a pre-fork racer (not just a send), so `base`
/// diverges in a receive's `rf`/value, the one case where re-derivability is least obvious. T4's
/// second receive reads a pre-fork racer in the "b" branch, but in the "a" branch the gated late
/// "int" revisits T4's first receive and deletes that second receive's established read.
fn attempt4() -> VdProgram {
    VdProgram {
        threads: vec![
            // T0 monitor
            vec![nbrecv(Sel::Eq("L"))],
            // T1 final relay → monitor
            vec![brecv(Sel::Eq("g")), send(0, "L", 0, 0)],
            // T2 feed final relay (late)
            vec![send(1, "g", 4, 4)],
            // T3 ep carrier: recv(=q); nd; SendIf(a → late "int" into T4)
            vec![
                brecv(Sel::Eq("q")),
                Op::Nondet,
                send_if(1, "a", 4, "int", 0, 0),
            ],
            // T4 intermediate victim: q feeder; two receives racing "int" + the pre-fork racers
            vec![
                send(3, "q", 1, 1),
                brecv(Sel::Any),
                brecv(Sel::Any),
            ],
            // T5, T6 pre-fork racers into T4 (established reads deleted differently per branch)
            vec![send(4, "p", 0, 1)],
            vec![send(4, "r", 0, 1)],
        ],
    }
}

// =====================================================================================
// γ4-biased randomized search (SplitMix64, no external crate).
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
    match rng.below(6) {
        0 => (0, 0),
        1 => (0, 1),
        2 => (1, 1),
        3 => (1, 2),
        4 => (2, 3),
        _ => (4, 5),
    }
}

/// Structured γ4 generator. Fixed skeleton (monitor + final relay + ep-carrier gating two
/// intermediate relays into one shared victim + pre-fork racers), windows/models/dsts/selectors
/// randomized. This structurally forces: a nondet po-after a receive (⇒ in `Deleted`), two
/// value-gated late relays (⇒ divergent intermediate revisits per branch), pre-fork racers into
/// the shared intermediate victim (⇒ candidate different deletions), and an independent final
/// late "L" revisiting the monitor from ≥ 2 branches.
fn gen_gamma4(rng: &mut Rng) -> VdProgram {
    let n = 7;
    let monitor = 0;
    let victim = 4; // intermediate victim
    let m = |rng: &mut Rng| if rng.chance(50) { Model::Asyn } else { Model::P2p };

    // Final relay chain windows.
    let (glo, ghi) = (2 + rng.below(3) as u64, 0);
    let ghi = ghi.max(glo + rng.below(2) as u64);

    // Two intermediate relays' windows.
    let (ulo, uhi) = rwin(rng);
    let (wlo, whi) = rwin(rng);
    // Pre-fork racer windows (near-tie).
    let (p1lo, p1hi) = rwin(rng);
    let (p2lo, p2hi) = rwin(rng);
    // q feeder window.
    let (qlo, qhi) = rwin(rng);

    let final_relay_sel = if rng.chance(50) { Sel::Eq("g") } else { Sel::Any };
    let victim_sel1 = if rng.chance(50) { Sel::Any } else { Sel::Eq("u") };
    let victim_sel2 = if rng.chance(50) { Sel::Any } else { Sel::Eq("w") };

    let threads = vec![
        // T0 monitor
        vec![nbrecv(if rng.chance(70) { Sel::Eq("L") } else { Sel::Any })],
        // T1 final relay → monitor (late L)
        vec![
            Op::Recv {
                sel: final_relay_sel,
                blocking: true,
            },
            Op::Send {
                dst: monitor,
                model: m(rng),
                val: "L",
                lo: 0,
                hi: 0,
            },
        ],
        // T2 feed final relay (late "g")
        vec![Op::Send {
            dst: 1,
            model: m(rng),
            val: "g",
            lo: glo,
            hi: ghi,
        }],
        // T3 ep carrier: recv(=q); nd; two mutually-exclusive gated late relays into T4
        vec![
            brecv(Sel::Eq("q")),
            Op::Nondet,
            Op::SendIf {
                guard: 1,
                eq: "a",
                dst: victim,
                model: m(rng),
                val: "u",
                lo: ulo,
                hi: uhi,
            },
            Op::SendIf {
                guard: 1,
                eq: "b",
                dst: victim,
                model: m(rng),
                val: "w",
                lo: wlo,
                hi: whi,
            },
        ],
        // T4 shared intermediate victim: two receives racing the gated relays and the racers
        vec![
            Op::Send {
                dst: 3,
                model: m(rng),
                val: "q",
                lo: qlo,
                hi: qhi,
            },
            Op::Recv {
                sel: victim_sel1,
                blocking: true,
            },
            Op::Recv {
                sel: victim_sel2,
                blocking: rng.chance(50),
            },
        ],
        // T5 pre-fork racer into T4
        vec![Op::Send {
            dst: victim,
            model: m(rng),
            val: "p",
            lo: p1lo,
            hi: p1hi,
        }],
        // T6 pre-fork racer into T4
        vec![Op::Send {
            dst: victim,
            model: m(rng),
            val: "r",
            lo: p2lo,
            hi: p2hi,
        }],
    ];
    let _ = n;
    VdProgram { threads }
}

/// Eager-suppression generator (reliably yields `viable == false`, the fixb pattern). A nondet
/// value gates a FAST send that eagerly beats a LATE timer at the final relay, so under that
/// value the relay reads the fast message and never emits the revisiting "L" — `viable(that value)`
/// is genuinely false. On top of that it keeps a pre-fork racer set and a second (intermediate)
/// victim so the false path co-occurs with divergent bases: the exact γ4 setting.
fn gen_eager(rng: &mut Rng) -> VdProgram {
    let m = |rng: &mut Rng| if rng.chance(50) { Model::Asyn } else { Model::P2p };
    // timer late; fast early enough to beat it (avail(fast) ≤ avail(timer)).
    let tlo = 4 + rng.below(3) as u64;
    let (flo, fhi) = (0u64, rng.below(2) as u64);
    // q feeds T3 early so ep's fast send has a small Occ.
    let (qlo, qhi) = (0u64, rng.below(2) as u64);
    // second-victim racer windows (near-tie), to seed divergent intermediate revisits.
    let (p1lo, p1hi) = rwin(rng);
    let (p2lo, p2hi) = rwin(rng);
    let (vlo, vhi) = rwin(rng); // gated send into the 2nd victim

    let victim2 = 4usize;
    let threads = vec![
        // T0 monitor (final revisit target): reads ⊥ or "L".
        vec![nbrecv(Sel::Eq("L"))],
        // T1 final relay: reads timer|fast; emits "L" ONLY when it read "timer".
        vec![
            brecv(Sel::Any),
            Op::SendIf {
                guard: 0,
                eq: "timer",
                dst: 0,
                model: m(rng),
                val: "L",
                lo: 0,
                hi: 0,
            },
        ],
        // T2 timer feeder (late) → relay.
        vec![Op::Send {
            dst: 1,
            model: m(rng),
            val: "timer",
            lo: tlo,
            hi: tlo,
        }],
        // T3 ep carrier: recv(=q); nd; SendIf(a → fast to the relay) + SendIf(b → late send to the
        // 2nd victim). ep sits po-after recv(=q) so it lands in the monitor-revisit's Deleted set.
        vec![
            brecv(Sel::Eq("q")),
            Op::Nondet,
            Op::SendIf {
                guard: 1,
                eq: "a",
                dst: 1,
                model: m(rng),
                val: "fast",
                lo: flo,
                hi: fhi,
            },
            Op::SendIf {
                guard: 1,
                eq: "b",
                dst: victim2,
                model: m(rng),
                val: "v",
                lo: vlo,
                hi: vhi,
            },
        ],
        // T4 q feeder + 2nd victim: send(3,"q") then a receive racing the racers / the gated "v".
        vec![
            Op::Send {
                dst: 3,
                model: m(rng),
                val: "q",
                lo: qlo,
                hi: qhi,
            },
            brecv(Sel::Any),
        ],
        // T5, T6 pre-fork racers into the 2nd victim (different one deleted per branch).
        vec![Op::Send {
            dst: victim2,
            model: m(rng),
            val: "p",
            lo: p1lo,
            hi: p1hi,
        }],
        vec![Op::Send {
            dst: victim2,
            model: m(rng),
            val: "r",
            lo: p2lo,
            hi: p2hi,
        }],
    ];
    VdProgram { threads }
}

// =====================================================================================
// The workhorse: run every builder + a search corpus, report duplicates & completeness.
// =====================================================================================

/// Assert the invariants that must hold regardless of γ4; return the report for tallying.
/// A T2 duplicate NOT present in T1/zombie is the γ4 hit and is printed here.
fn vet(name: &str, prog: &VdProgram, verbose: bool, hits: &mut Vec<(String, Vec<String>)>) -> Report {
    let rep = run_all(prog);

    // Completeness is the load-bearing invariant. A T2-vs-T1 full-set divergence is a SEPARATE,
    // more serious finding (a lost or spurious realizable terminal) — surface it loudly.
    assert!(
        rep.zombie_ok(),
        "{name}: zombie full-set != T1-filter full-set (arbiter broke)\n  prog={prog:#?}",
    );
    assert!(
        rep.complete(),
        "{name}: COMPLETENESS FINDING — T2 realizable full-set != T1-filter full-set.\n  \
         T1\\T2 = {:?}\n  T2\\T1 = {:?}\n  prog={prog:#?}",
        rep.t1_full.difference(&rep.t2_full).collect::<Vec<_>>(),
        rep.t2_full.difference(&rep.t1_full).collect::<Vec<_>>(),
    );

    if verbose {
        println!(
            "  [{name}] t1_full={} t2_full={} t2_terms={} dead={} revisits={} viable_calls={} (false={})",
            rep.t1_full.len(),
            rep.t2_full.len(),
            rep.t2_terms.len(),
            rep.dead,
            rep.revisits.len(),
            rep.viable_calls.len(),
            rep.viable_calls.iter().filter(|c| !c.4).count(),
        );
    }

    // The DIRECT γ4 danger signal: a base-content-dependent verdict (same oracle question, ≥2
    // bases, disagreeing). B1.b assumes this never happens; γ4 is exactly the hypothesis that it
    // can. If it EVER fires we surface it loudly (whether or not it happened to cause a duplicate
    // in this run), because it is the mechanism, not just the symptom.
    let bdv = rep.base_dependent_verdicts();
    if !bdv.is_empty() {
        println!("  ??? [{name}] BASE-DEPENDENT viable verdict (γ4 precondition!) for (s,ep,v)={bdv:#?}");
        println!("      viable calls: {:#?}", rep.viable_calls);
        println!("      program: {prog:#?}");
    }

    if rep.t2_has_dup() {
        let dups = rep.dup_keys();
        println!("  !!! [{name}] T2 DUPLICATE canonical keys: {dups:#?}");
        println!("      revisits (r,s,deleted): {:#?}", rep.revisits);
        println!("      viable calls (base_key, ep, v, s, verdict): {:#?}", rep.viable_calls);
        println!("      program: {prog:#?}");
        hits.push((name.to_string(), dups));
    }
    rep
}

/// Coverage + result tallies accumulated across the whole search.
#[derive(Default)]
struct Tally {
    progs: usize,
    with_revisit: usize,
    with_viable: usize,
    with_false: usize,
    /// programs where the same oracle question was posed against ≥ 2 distinct bases (γ4 setting).
    with_multi_base: usize,
    /// programs where such multi-base questions DISAGREED on the verdict (the γ4 precondition).
    with_base_dependent: usize,
    max_terms: usize,
}

impl Tally {
    fn absorb(&mut self, rep: &Report) {
        self.progs += 1;
        self.with_revisit += usize::from(!rep.revisits.is_empty());
        self.with_viable += usize::from(!rep.viable_calls.is_empty());
        self.with_false += usize::from(rep.viable_calls.iter().any(|c| !c.4));
        self.with_multi_base += usize::from(rep.multi_base_questions() > 0);
        self.with_base_dependent += usize::from(!rep.base_dependent_verdicts().is_empty());
        self.max_terms = self.max_terms.max(rep.t2_terms.len());
    }
}

/// The single machine-verification test. Drives the directed shapes and two randomized corpora
/// (a SendIf-divergence generator and an eager-suppression generator that reliably produces the
/// `viable == false` path); asserts completeness throughout; records any reproduced duplicate and
/// any base-dependent verdict (the γ4 mechanism itself).
#[test]
fn gamma4_machine_verification() {
    let mut hits: Vec<(String, Vec<String>)> = Vec::new();
    let mut tally = Tally::default();

    // Directed hand-built attempts.
    for (name, prog) in [
        ("attempt1", attempt1()),
        ("attempt2", attempt2()),
        ("attempt3", attempt3()),
        ("attempt4", attempt4()),
    ] {
        let rep = vet(name, &prog, true, &mut hits);
        tally.absorb(&rep);
    }

    // Two randomized corpora.
    let each = if cfg!(debug_assertions) { 700 } else { 6000 };
    let mut rng = Rng::new(0x6A11_0426_2026);
    for case in 0..each {
        let prog = gen_gamma4(&mut rng);
        let rep = vet(&format!("g4#{case}"), &prog, false, &mut hits);
        tally.absorb(&rep);
    }
    for case in 0..each {
        let prog = gen_eager(&mut rng);
        let rep = vet(&format!("eg#{case}"), &prog, false, &mut hits);
        tally.absorb(&rep);
    }

    println!(
        "γ4 search: {} programs | with_revisit={} with_viable={} with_viable_false={} \
         with_multi_base={} with_base_dependent={} max_terms={} | DUPLICATES={}",
        tally.progs,
        tally.with_revisit,
        tally.with_viable,
        tally.with_false,
        tally.with_multi_base,
        tally.with_base_dependent,
        tally.max_terms,
        hits.len(),
    );

    // Non-degeneracy floors: the corpus must actually exercise the FULL mechanism — backward
    // revisits, the non-min PASS oracle, its FALSE path, and (critically) the same question posed
    // against divergent bases — or a "no duplicate" result would be vacuous.
    assert!(
        tally.with_revisit >= tally.progs / 5,
        "corpus too weak: only {}/{} programs performed a backward revisit",
        tally.with_revisit,
        tally.progs,
    );
    assert!(
        tally.with_viable >= 50,
        "corpus too weak: the non-min PASS oracle fired on only {} programs",
        tally.with_viable,
    );
    assert!(
        tally.with_false >= 5,
        "corpus too weak: the viable oracle returned false on only {} programs (need the false \
         path — the eager-suppression generator should force it)",
        tally.with_false,
    );
    assert!(
        tally.with_multi_base >= 5,
        "corpus too weak: only {} programs posed the SAME oracle question against ≥2 bases — γ4 \
         needs divergent bases for one question, so this is the setting we must cover",
        tally.with_multi_base,
    );

    // The DIRECT invariant: no base-dependent verdict was EVER observed. This is the machine
    // confirmation of the B1.f-2 re-derivability invariant — the verdict of `viable` is a pure
    // function of the ep-independent forward-closure, so divergent bases cannot flip it, so γ4
    // cannot manufacture a duplicate.
    assert_eq!(
        tally.with_base_dependent, 0,
        "γ4 PRECONDITION OBSERVED: {} program(s) had a base-content-dependent viable verdict. \
         Inspect the '??? BASE-DEPENDENT' dumps above — a duplicate may be reachable by tuning.",
        tally.with_base_dependent,
    );

    // RESULT. A non-empty `hits` is a reproduced optimality-(a) duplicate (completeness held —
    // asserted in `vet`): the REPRODUCED verdict. Otherwise NO-REPRO.
    assert!(
        hits.is_empty(),
        "γ4 REPRODUCED: {} program(s) produced a T2 duplicate canonical key that T1/zombie did \
         not, with completeness intact. Details above.\n{hits:#?}",
        hits.len(),
    );
    // NO-REPRO: no duplicate under any directed or randomized γ4-shaped program; completeness
    // (T2 full == T1 full) held on every one; and no viable verdict was ever base-dependent. See
    // the FINDING block at the file tail.
}

// =====================================================================================
// γ4 v2 — the SHARPENED recipe: a differently-deleted pre-fork send BEHIND A CHOICE POINT.
//
// The first NO-REPRO's generators never placed a differently-deleted send behind a choice point.
// The adversarial theory says `viable`'s forward drain (step 1 of `viable_search`) drains only
// *forced* events (send / error / SINGLETON nondet); a MULTI-value nondet or a blocking receive
// PARKS the drain. So a pre-fork send positioned po-after a 2-value nondet on its thread is:
//   * PERMANENT when its base has the nondet already resolved to the emitting value (present-unread
//     ⇒ the forward search can never delete it — an unavoidable competitor, Leak 2), but
//   * RE-DERIVABLE-EITHER-WAY when its base had the nondet+send deleted (the search re-forks the
//     nondet and can pick the NON-emitting value ⇒ a completion without the send, Leak 1).
// Two sibling ep-branches whose intermediate revisits delete this send in one but resolve it
// present in the other then feed `viable` two bases that disagree ⇒ `with_base_dependent > 0`,
// the γ4 precondition. These builders plant exactly that shape (the cheap nondet choice point —
// no feeder thread — is the "multi-value nondet" park the recipe names).
// =====================================================================================

/// A racer thread whose send sits BEHIND a 2-value nondet choice point: `[nd{a,b}; SendIf(nd==a →
/// send(dst,val,[lo,hi]))]`. In `viable_search` the drain parks at the `nd` (multi-value) and only
/// re-emits the send after a branch picks "a" — the Leak-1/2 park.
fn racer_behind_nondet(dst: usize, val: &'static str, lo: u64, hi: u64) -> Vec<Op> {
    vec![Op::Nondet, send_if(0, "a", dst, val, lo, hi)]
}

/// Directed leak attempt A — a fast COMPETITOR to the monitor, behind a nondet park (Leak 2).
///  * T0 monitor `brecv(=L)` = r_final, Occ=0 (no A-clause escape).
///  * T1 `brecv(=g); send(0,"L",[0,0])` = the LATE s_final (g fed late ⇒ avail(L) late).
///  * T2 feeds g late.
///  * T3 ep carrier: `brecv(=q); nd{a,b}; SendIf(a→u victim); SendIf(b→w victim)` — divergent
///    intermediate revisits into the shared victim T4.
///  * T4 victim `send(3,q); brecv(any)`.
///  * T5 racer-behind-nondet: a FAST "L" to the monitor (competitor of r_final←s_final), parked
///    behind its own 2-value nondet.
fn leak_a() -> VdProgram {
    VdProgram {
        threads: vec![
            vec![brecv(Sel::Eq("L"))],
            vec![brecv(Sel::Eq("g")), send(0, "L", 0, 0)],
            vec![send(1, "g", 4, 4)],
            vec![
                brecv(Sel::Eq("q")),
                Op::Nondet,
                send_if(1, "a", 4, "u", 0, 0),
                send_if(1, "b", 4, "w", 0, 0),
            ],
            vec![send(3, "q", 1, 1), brecv(Sel::Any)],
            racer_behind_nondet(0, "L", 0, 0),
        ],
    }
}

/// Directed leak attempt B — a SOURCE behind a nondet park feeding the victim's read (Leak 1),
/// plus a second parked racer, so two pre-fork parked sends can be deleted differently per branch.
fn leak_b() -> VdProgram {
    VdProgram {
        threads: vec![
            vec![brecv(Sel::Eq("L"))],
            vec![brecv(Sel::Eq("g")), send(0, "L", 0, 0)],
            vec![send(1, "g", 4, 4)],
            vec![
                brecv(Sel::Eq("q")),
                Op::Nondet,
                send_if(1, "a", 4, "u", 0, 0),
                send_if(1, "b", 4, "w", 0, 0),
            ],
            vec![send(3, "q", 1, 1), brecv(Sel::Any), brecv(Sel::Any)],
            racer_behind_nondet(4, "p", 0, 1),
            racer_behind_nondet(0, "L", 0, 0),
        ],
    }
}

/// γ4-v2 randomized generator: the divergent-intermediate-revisit skeleton of `gen_gamma4`, but
/// the pre-fork racers are now PARKED behind their own 2-value nondets and some target the MONITOR
/// (competitors of the final revisit), which is the choice-point-behind-send shape the first
/// NO-REPRO never built. Windows/models/dsts/selectors randomized.
fn gen_leak(rng: &mut Rng) -> VdProgram {
    let victim = 4usize;
    let monitor = 0usize;
    let m = |rng: &mut Rng| if rng.chance(50) { Model::Asyn } else { Model::P2p };

    let glo = 2 + rng.below(3) as u64;
    let (ulo, uhi) = rwin(rng);
    let (wlo, whi) = rwin(rng);
    // Parked-racer windows: keep them FAST (small) so a monitor-targeting one is a live
    // competitor to the late s_final.
    let (c1lo, c1hi) = (0u64, rng.below(2) as u64);
    let (c2lo, c2hi) = (0u64, rng.below(2) as u64);
    let (qlo, qhi) = rwin(rng);

    // Where each parked racer aims: monitor (competitor of r_final) or victim (intermediate).
    let dst1 = if rng.chance(60) { monitor } else { victim };
    let dst2 = if rng.chance(60) { monitor } else { victim };
    let val1 = if dst1 == monitor { "L" } else { "p" };
    let val2 = if dst2 == monitor { "L" } else { "r" };

    let victim_sel1 = if rng.chance(50) { Sel::Any } else { Sel::Eq("u") };
    let victim_sel2 = if rng.chance(50) { Sel::Any } else { Sel::Eq("w") };

    let threads = vec![
        // T0 monitor = r_final.
        vec![brecv(Sel::Eq("L"))],
        // T1 late relay = s_final.
        vec![
            brecv(Sel::Eq("g")),
            Op::Send {
                dst: monitor,
                model: m(rng),
                val: "L",
                lo: 0,
                hi: 0,
            },
        ],
        // T2 late g feeder.
        vec![Op::Send {
            dst: 1,
            model: m(rng),
            val: "g",
            lo: glo,
            hi: glo,
        }],
        // T3 ep carrier: divergent intermediate revisits into the shared victim.
        vec![
            brecv(Sel::Eq("q")),
            Op::Nondet,
            Op::SendIf {
                guard: 1,
                eq: "a",
                dst: victim,
                model: m(rng),
                val: "u",
                lo: ulo,
                hi: uhi,
            },
            Op::SendIf {
                guard: 1,
                eq: "b",
                dst: victim,
                model: m(rng),
                val: "w",
                lo: wlo,
                hi: whi,
            },
        ],
        // T4 shared victim (one or two receives).
        {
            let mut v = vec![
                Op::Send {
                    dst: 3,
                    model: m(rng),
                    val: "q",
                    lo: qlo,
                    hi: qhi,
                },
                Op::Recv {
                    sel: victim_sel1,
                    blocking: true,
                },
            ];
            if rng.chance(60) {
                v.push(Op::Recv {
                    sel: victim_sel2,
                    blocking: rng.chance(50),
                });
            }
            v
        },
        // T5, T6 parked racers (behind a 2-value nondet).
        racer_behind_nondet(dst1, val1, c1lo, c1hi),
        racer_behind_nondet(dst2, val2, c2lo, c2hi),
    ];
    VdProgram { threads }
}

/// γ4-v2 generator #2 — the eager-suppression FALSE path (`gen_eager`) crossed with an
/// ep-INDEPENDENT parked competitor to the relay. The relay `[brecv(Any); SendIf(read "timer" →
/// L)]` emits the final s_final only if it read the (late) "timer"; a FAST send to the relay is a
/// competitor that (Occ(relay)=0) makes reading "timer" eager-infeasible, so the relay reads the
/// fast and never emits L ⇒ `viable == false`. Here that fast source is a PARKED, pre-fork,
/// ep-independent racer (`[nd{a,b}; SendIf(a → fast→relay)]`), so — if any base ever carried it
/// present-unread — a base with it resolved-present ("a") would answer FALSE while a base that
/// deleted it (parked, re-forkable to "b") would answer TRUE: the exact base-dependence γ4 needs.
fn gen_eager_parked(rng: &mut Rng) -> VdProgram {
    let m = |rng: &mut Rng| if rng.chance(50) { Model::Asyn } else { Model::P2p };
    let tlo = 3 + rng.below(3) as u64; // timer late enough for a fast to beat it
    let (qlo, qhi) = (0u64, rng.below(2) as u64);
    let (p1lo, p1hi) = rwin(rng);
    let (p2lo, p2hi) = rwin(rng);
    let victim2 = 4usize;

    let threads = vec![
        // T0 monitor = r_final (NON-blocking: reads ⊥ or the late "L", so the "L never emitted"
        // suppression is a valid terminal that the late "L" can backward-revisit ⇒ the false path).
        vec![nbrecv(Sel::Eq("L"))],
        // T1 relay: reads Any; emits L only when it read "timer".
        vec![
            brecv(Sel::Any),
            Op::SendIf {
                guard: 0,
                eq: "timer",
                dst: 0,
                model: m(rng),
                val: "L",
                lo: 0,
                hi: 0,
            },
        ],
        // T2 timer feeder (late).
        vec![Op::Send {
            dst: 1,
            model: m(rng),
            val: "timer",
            lo: tlo,
            hi: tlo,
        }],
        // T3 ep carrier: recv(=q); nd; SendIf(a→ fast to relay); SendIf(b→ v into victim2). The
        // fast under ep="a" is the ep-DEPENDENT suppressor (cone) — the false path.
        vec![
            brecv(Sel::Eq("q")),
            Op::Nondet,
            Op::SendIf {
                guard: 1,
                eq: "a",
                dst: 1,
                model: m(rng),
                val: "fast",
                lo: 0,
                hi: 0,
            },
            Op::SendIf {
                guard: 1,
                eq: "b",
                dst: victim2,
                model: m(rng),
                val: "vv",
                lo: p1lo,
                hi: p1hi,
            },
        ],
        // T4 q feeder + 2nd victim.
        vec![
            Op::Send {
                dst: 3,
                model: m(rng),
                val: "q",
                lo: qlo,
                hi: qhi,
            },
            brecv(Sel::Any),
        ],
        // T5 ep-INDEPENDENT parked competitor to the relay: a fast "fast" behind a 2-value nondet.
        racer_behind_nondet(1, "fast", 0, 0),
        // T6 ep-independent parked racer into victim2.
        racer_behind_nondet(victim2, "r", p2lo, p2hi),
    ];
    VdProgram { threads }
}

/// The γ4-v2 hunt: drives the sharpened choice-point-behind-send shapes and reports whether the
/// `viable` verdict is ever base-content-dependent (`with_base_dependent`), whether that ever
/// co-occurs with a hosted backward revisit, and whether any T2 duplicate materialises — all with
/// completeness (T2 full == T1 full) asserted throughout by `vet`.
#[test]
fn gamma4_leak_hunt() {
    let mut hits: Vec<(String, Vec<String>)> = Vec::new();
    let mut tally = Tally::default();
    // Every (name, program, report) whose viable verdict was base-dependent, for the tail summary.
    let mut bdv_reports: Vec<String> = Vec::new();

    let mut note = |name: &str, rep: &Report| {
        let bdv = rep.base_dependent_verdicts();
        if bdv.is_empty() {
            return;
        }
        // Did a base-dependent (s,ep,v) actually host a backward revisit whose s == that send?
        let hosted: bool = bdv.iter().any(|(s, _ep, _v)| {
            rep.revisits.iter().any(|(_r, rs, _del)| rs == s)
        });
        bdv_reports.push(format!(
            "{name}: base-dependent (s,ep,v)={bdv:?} hosted_revisit={hosted} dup={}",
            rep.t2_has_dup()
        ));
    };

    for (name, prog) in [("leak_a", leak_a()), ("leak_b", leak_b())] {
        let rep = vet(name, &prog, true, &mut hits);
        note(name, &rep);
        tally.absorb(&rep);
    }

    let each = if cfg!(debug_assertions) { 1500 } else { 20000 };
    let mut rng = Rng::new(0x1EAC_2026_0725);
    for case in 0..each {
        let prog = gen_leak(&mut rng);
        let rep = vet(&format!("leak#{case}"), &prog, false, &mut hits);
        note(&format!("leak#{case}"), &rep);
        tally.absorb(&rep);
    }
    for case in 0..each {
        let prog = gen_eager_parked(&mut rng);
        let rep = vet(&format!("egp#{case}"), &prog, false, &mut hits);
        note(&format!("egp#{case}"), &rep);
        tally.absorb(&rep);
    }

    println!(
        "γ4-v2 hunt: {} programs | with_revisit={} with_viable={} with_viable_false={} \
         with_multi_base={} with_base_dependent={} max_terms={} | DUPLICATES={}",
        tally.progs,
        tally.with_revisit,
        tally.with_viable,
        tally.with_false,
        tally.with_multi_base,
        tally.with_base_dependent,
        tally.max_terms,
        hits.len(),
    );
    if !bdv_reports.is_empty() {
        println!("  base-dependent programs ({}):", bdv_reports.len());
        for r in bdv_reports.iter().take(40) {
            println!("    {r}");
        }
    }

    // Non-degeneracy: the shape must actually exercise divergent bases for one question AND the
    // viable oracle's FALSE path (the verdict a base-dependence flip needs a witness of).
    assert!(
        tally.with_multi_base >= 5,
        "corpus too weak: only {} programs posed one question against ≥2 bases",
        tally.with_multi_base,
    );
    assert!(
        tally.with_false >= 50,
        "corpus too weak: the viable oracle returned false on only {} programs — the \
         choice-point-behind-send false path must be covered for the NO-REPRO to bind",
        tally.with_false,
    );

    // Completeness is asserted per-program inside `vet`. A duplicate is the REPRODUCED signal.
    assert!(
        hits.is_empty(),
        "γ4 REPRODUCED: {} program(s) produced a T2 duplicate T1/zombie did not, completeness \
         intact.\n{hits:#?}",
        hits.len(),
    );
}

// =====================================================================================
// ==== FINDING (γ4 / risk R5) — NO-REPRO ====
//
// Verdict: NO-REPRO. Under `.with_time_predicate()`, no value-dependent program in this file —
// 4 directed hand-built shapes + 12000 randomized (release) — produced a duplicate canonical key
// among terminals; T2's realizable `full_keys` equalled the `.with_time_filter()` (T1) set on
// every program (completeness intact, verified in `vet`); and the `.with_time_zombie()` arbiter
// matched T1 throughout.
//
// Coverage (release, 12004 programs): with_revisit=12004, with_viable=11020, with_viable_false=
// 6000, with_multi_base=794, with_base_dependent=0, DUPLICATES=0. The corpus is NOT vacuous: it
// forces backward revisits, the non-min PASS oracle, the oracle's FALSE path, and — the point of
// γ4 — the same oracle question `(revisiting s, ep, tested v)` evaluated against ≥2 DIFFERENT
// `base` graphs (794 programs). In every one of those 794 divergent-base settings the verdict
// agreed, so no branch could double-PASS a shared `g2`.
//
// Why it is structurally blocked (the named invariant, machine-confirmed):
//   `viable(base, ep, v, …)` searches FORWARD completions of `base` (drain forced events, branch
//   over choice points from the frontier). `base = Previous(ep) \ cone(ep)`. Two sibling branches
//   of the fork `ep` can reach the final revisit via DIFFERENT intermediate revisits that delete
//   DIFFERENT pre-fork events, so `base¹ ≠ base²` as raw content — γ4's premise is real. But each
//   such difference is one of:
//     (i)  ep-dependent  ⇒ in `cone(ep)` ⇒ `viability_base` drops it from BOTH bases identically;
//     (ii) ep-independent pre-fork content deleted by an ep-caused intermediate revisit ⇒ a
//          po-suffix-closed hole (restrict keeps po-prefixes) whose events the forward search
//          re-emits deterministically from the (ep-independent) frontier trace.
//   Hence `viable`'s verdict depends only on the ep-independent forward-closure of `base`, not on
//   `base`'s raw content: `viable(base¹, v) == viable(base², v)`. That is exactly B1.b's assumed
//   holder-independence OF THE VERDICT (O1), which γ4 tried to break at the level of raw `base`
//   content but cannot break at the level of the forward-closure the oracle actually consumes.
//   Equivalently: "`Previous(ep,s) \ kept` is uniquely re-derivable from `g2` + the program"
//   (the B1.f-2 candidate) — confirmed here as `with_base_dependent == 0`.
//
// Caveat / scope: this is empirical refutation of the *reproduction recipe*, not a closed proof of
// R5. The `with_base_dependent` detector is the tightest live probe of the γ4 precondition; should
// a future program ever trip it (the `??? BASE-DEPENDENT` dump), that is the seed to escalate. The
// existential oracle is separately proven one-sided (spurious-true excluded, `T2_PROOFS_A.md`), so
// even an unfound γ4 duplicate could only ever DUPLICATE, never lose a realizable terminal.
