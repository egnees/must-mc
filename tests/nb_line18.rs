//! **γ3-hard witness, arm line 18** (`T2_GAMMA_FRONTIER` §Ⅱ recipes R-1 / R-2): the predicted
//! *third* completeness loss of T2, and the pinned witness that a viability-aware non-blocking
//! canon (`pass_nb`) fixes it.
//!
//! # The hole
//!
//! `revisit.rs` line 18 calls a **non-blocking** receive in `Deleted` canonical iff it reads ⊥,
//! justified by *local* feasibility ("nb is time-transparent, so ⊥ is always feasible"). What the
//! canon needs is **viability**: reading ⊥ leaves the message unconsumed, so the ⊥ branch may emit
//! an early-window competitor that kills the region through the B-clause *before* the revisiting
//! send is emitted. The canonical branch then never produces the revisiting send, the branch that
//! does produce it is refused as non-canonical, and the revisit fires from nowhere.
//!
//! This is the exact structural twin of two defects that were already real bugs:
//! the *nondet* arm (raft f1 28-vs-40) and the *blocking-receive* arm line 22
//! (`tests/r1_line22.rs`, 3-vs-2) — both fixed by an existential PASS rule.
//!
//! # Shape (R-1)
//!
//! ```text
//! T0: r  := recv_nb(= "L")                        // victim; DES adds it first (LB 0, tid 0)
//! T1: s  := send(T2, "s", [0,0])
//!     m  := send(T3, "m", [150,150])
//! T2: ep := recv_nb(= "s")                        // lands in Deleted
//!     if ep == ⊥ { c := send(T3, "c", [0,0]) }    // killer ONLY on the ⊥ (old-canonical) read
//! T3: q  := recv(= "m" | = "c")                   // blocking
//!     if q == "m" { L := send(T0, "L") }          // the revisiting send
//! ```
//!
//! `ep ← s`  ⇒ no killer ⇒ `q ← m` is the only read ⇒ `L` exists ⇒ revisit candidate, but
//! `ep ∈ Deleted` reads `s`, so line 18 is false and the revisit is **rejected**.
//! `ep ← ⊥`  ⇒ `c@[0,0]` is emitted ⇒ `q ← m` is eager-infeasible (A: `avail(m)=150 ≤ Occ(q)=0`
//! ✗; B: `avail(c)=0 ≥ avail(m)=150` ✗) ⇒ T-PRED prunes it ⇒ `L` never appears there.
//! So `L` exists **only** where `ep` is non-canonical, and the terminal `(r←L, ep←s, q←m)` is lost.
//!
//! R-2 is R-1 plus a `nondet{"a","b"}` on T2 ahead of `ep`, with the killer conditioned on
//! `ep == ⊥ ∧ X == "a"`: three `r←L` terminals instead of one, and it also exercises the
//! interaction with the nondet arm's PASS rule.
//!
//! # What is asserted
//!
//! # This file is the ONLY live coverage of the `pass_nb` branch — keep it pinned forever
//!
//! Measured on the merged tree (`tests/ladder.rs`, July 2026): outside these two witnesses
//! `pass_nb` does not change a single verdict. Re-running every corpus before and after the merge
//! gives *bit-identical* statistics — visits, dead, filtered, duplicates, oracle calls, divergence
//! rates — on 250 + 3000 timed, 150 + 2000 value-dependent and 300 + 3000 canon-directed programs,
//! and identical realizable key sets on raft f0 / f1 / `--bug`. The corpora are structurally blind
//! to the shape: it needs a **non-⊥ non-blocking read inside `Deleted`** whose ⊥ alternative emits
//! an early-window competitor, and none of the generators produces that (the canon-directed one's
//! only non-blocking receive is the revisit *victim*, which is never in `Deleted`).
//!
//! Consequence: a green corpus is **not** evidence about this branch. Deleting or relaxing this
//! file would leave `pass_nb` — a completeness fix — with zero test coverage.
//!
//! Three-way arbitration over **every** priority permutation: `realizable(T2-predicate) ==
//! realizable(zombie) == realizable(T1-filter)`, as *sets of `canonical_key`s*. Zombie and T1 are
//! correct by construction (untimed Algorithm 1 + the proven terminal filter), so the equality is
//! a genuine certificate, not a self-consistency check. The counts are pinned (R-1: 3, R-2: 7) —
//! do not relax them; a change means the witness stopped exercising the shape.

use std::collections::BTreeSet;

use must::event::{Label, Model, Pred, Window};
use must::{explore, Config, CountingObserver, ExecutionCollector, Program, ThreadNext, Val};

type NextFn = fn(&[Option<Val>]) -> ThreadNext;
type FutureFn = fn(&[Option<Val>]) -> Option<Vec<Label>>;

struct Vdp {
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

/// The victim: a non-blocking receive on T0, added first by DES, revisited by `L`.
fn r_nb() -> Label {
    Label::recv_nb(Pred::eq("L"))
}
/// The message the `Deleted` non-blocking receive may consume — early, so it is never a
/// competitor of anything.
fn s_send() -> Label {
    Label::send_within(Model::Asyn, 2, "s", Window::new(0, 0))
}
/// The late message `q` must read for `L` to exist.
fn m_send() -> Label {
    Label::send_within(Model::Asyn, 3, "m", Window::new(150, 150))
}
/// The `Deleted` non-blocking receive itself.
fn ep_lbl() -> Label {
    Label::recv_nb(Pred::eq("s"))
}
/// The killer: an early competitor of `m`, emitted only when `ep` leaves `s` unconsumed.
fn c_send() -> Label {
    Label::send_within(Model::Asyn, 3, "c", Window::new(0, 0))
}
/// The blocking receive whose read decides whether `L` is emitted.
fn q_lbl() -> Label {
    Label::recv(Pred::new("=m|=c", |x| x == "m" || x == "c"))
}
/// The revisiting send (untimed `[0, ∞)`).
fn l_send() -> Label {
    Label::send(Model::Asyn, 0, "L")
}
/// R-2 only: the nondet ahead of `ep`, whose arm is the second half of the composite.
fn x_nd() -> Label {
    Label::nondet(["a", "b"])
}

// -- R-1 threads ----------------------------------------------------------------------------

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
        0 => ThreadNext::Next(s_send()),
        1 => ThreadNext::Next(m_send()),
        _ => ThreadNext::Finished,
    }
}
fn t1_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![s_send(), m_send()],
        1 => vec![m_send()],
        _ => vec![],
    })
}

fn t2(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(ep_lbl()),
        // ⊥ read (`None`) ⇒ `s` stays unconsumed ⇒ emit the killer.
        1 if trace[0].is_none() => ThreadNext::Next(c_send()),
        _ => ThreadNext::Finished,
    }
}
fn t2_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![ep_lbl(), c_send()],
        1 if trace[0].is_none() => vec![c_send()],
        _ => vec![],
    })
}

fn t3(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(q_lbl()),
        1 if is(&trace[0], "m") => ThreadNext::Next(l_send()),
        _ => ThreadNext::Finished,
    }
}
fn t3_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![q_lbl(), l_send()],
        1 if is(&trace[0], "m") => vec![l_send()],
        _ => vec![],
    })
}

fn prog_r1() -> Vdp {
    Vdp {
        nexts: vec![t0, t1, t2, t3],
        futures: vec![t0_future, t1_future, t2_future, t3_future],
    }
}

// -- R-2 threads (R-1 + a nondet ahead of `ep`) ----------------------------------------------

fn t2_nd(trace: &[Option<Val>]) -> ThreadNext {
    match trace.len() {
        0 => ThreadNext::Next(x_nd()),
        1 => ThreadNext::Next(ep_lbl()),
        // killer only on (⊥ read) ∧ (X == "a")
        2 if trace[1].is_none() && is(&trace[0], "a") => ThreadNext::Next(c_send()),
        _ => ThreadNext::Finished,
    }
}
fn t2_nd_future(trace: &[Option<Val>]) -> Option<Vec<Label>> {
    Some(match trace.len() {
        0 => vec![x_nd(), ep_lbl(), c_send()],
        1 => vec![ep_lbl(), c_send()],
        2 if trace[1].is_none() && is(&trace[0], "a") => vec![c_send()],
        _ => vec![],
    })
}

fn prog_r2() -> Vdp {
    Vdp {
        nexts: vec![t0, t1, t2_nd, t3],
        futures: vec![t0_future, t1_future, t2_nd_future, t3_future],
    }
}

// -- harness ---------------------------------------------------------------------------------

fn keys(col: &ExecutionCollector) -> BTreeSet<String> {
    col.terminal_keys().into_iter().collect()
}

/// Every permutation of `0..n` in lexicographic order (n ≤ 4 here, so 24 at most).
fn permutations(n: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut cur: Vec<usize> = (0..n).collect();
    loop {
        out.push(cur.clone());
        // next lexicographic permutation
        let Some(i) = (0..n.saturating_sub(1)).rev().find(|&i| cur[i] < cur[i + 1]) else {
            break;
        };
        let j = (i + 1..n).rev().find(|&j| cur[j] > cur[i]).unwrap();
        cur.swap(i, j);
        cur[i + 1..].reverse();
    }
    out
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    Filter,
    Zombie,
    Predicate,
}

fn cfg(mode: Mode, priorities: &[usize]) -> Config {
    let base = Config::default()
        .collect_errors()
        .with_priorities(priorities.to_vec());
    match mode {
        Mode::Filter => base.with_time_filter(),
        Mode::Zombie => base.with_time_zombie(),
        Mode::Predicate => base.with_time_predicate(),
    }
}

/// Run one mode under one priority permutation, returning `(keys, full, blocked, terminals)`.
/// `terminals` is the raw reported count — a duplicate `canonical_key` shows up as
/// `terminals > keys.len()`.
fn run<MK, P>(make: MK, mode: Mode, priorities: &[usize]) -> (BTreeSet<String>, usize, usize, usize)
where
    MK: Fn() -> P + Sync,
    P: Program,
{
    let col = ExecutionCollector::new();
    let cnt = CountingObserver::new();
    let obs = (col, cnt);
    explore(make, &obs, cfg(mode, priorities));
    let (col, cnt) = obs;
    let n = col.terminal_keys().len();
    (keys(&col), cnt.full(), cnt.blocked(), n)
}

/// The shared body of both witnesses: three-way arbitration over **every** priority permutation.
///
/// Every permutation is run and printed *before* anything is asserted, so a regression reports
/// the whole picture (which permutations diverge, and by which keys) instead of dying on the
/// first one. Divergences are accumulated and re-raised at the end.
fn arbitrate<MK, P>(make: MK, name: &str, expected: usize)
where
    MK: Fn() -> P + Sync + Copy,
    P: Program,
{
    let n = make().num_threads();
    let mut reference: Option<BTreeSet<String>> = None;
    let mut failures: Vec<String> = Vec::new();
    for perm in permutations(n) {
        let (t1_keys, t1_full, t1_blocked, t1_n) = run(make, Mode::Filter, &perm);
        let (z_keys, ..) = run(make, Mode::Zombie, &perm);
        let (t2_keys, t2_full, t2_blocked, t2_n) = run(make, Mode::Predicate, &perm);

        eprintln!(
            "{name} perm={perm:?}: T1 keys={} (full={t1_full} blocked={t1_blocked} raw={t1_n}) \
             zombie keys={} T2 keys={} (full={t2_full} blocked={t2_blocked} raw={t2_n})",
            t1_keys.len(),
            z_keys.len(),
            t2_keys.len(),
        );
        // A raw terminal count above the key count is a duplicate `canonical_key`.
        if t1_n != t1_keys.len() {
            failures.push(format!("{perm:?}: T1 duplicate key ({t1_n} raw vs {})", t1_keys.len()));
        }
        if t2_n != t2_keys.len() {
            failures.push(format!("{perm:?}: T2 duplicate key ({t2_n} raw vs {})", t2_keys.len()));
        }
        // The reference is priority-invariant by Theorem 4.1.
        match &reference {
            None => {
                for k in &t1_keys {
                    eprintln!("  REF {k}");
                }
                reference = Some(t1_keys.clone());
            }
            Some(r) => {
                if &t1_keys != r {
                    failures.push(format!("{perm:?}: T1-filter is not priority-invariant"));
                }
            }
        }
        if z_keys != t1_keys {
            failures.push(format!("{perm:?}: zombie != T1-filter"));
        }
        if t2_keys != t1_keys {
            for k in t1_keys.difference(&t2_keys) {
                eprintln!("  LOST BY T2 ({perm:?}): {k}");
            }
            for k in t2_keys.difference(&t1_keys) {
                eprintln!("  EXTRA IN T2 ({perm:?}): {k}");
            }
            failures.push(format!(
                "{perm:?}: T2 realizable set differs from the reference \
                 (T2 {} vs ref {}, lost {}, extra {})",
                t2_keys.len(),
                t1_keys.len(),
                t1_keys.difference(&t2_keys).count(),
                t2_keys.difference(&t1_keys).count(),
            ));
        }
    }
    assert!(failures.is_empty(), "{name}: {} divergence(s):\n  {}", failures.len(), failures.join("\n  "));
    assert_eq!(
        reference.expect("at least one permutation").len(),
        expected,
        "{name}: the witness must have exactly {expected} realizable terminals"
    );
}

/// R-1: the minimal line-18 witness (4 threads, no nondet). Predicted pre-fix: T1 == zombie == 3,
/// T2 == 2, losing `(r←L, ep←s, q←m)`.
#[test]
fn nb_line18_witness() {
    arbitrate(prog_r1, "R-1", 3);
}

/// R-2: R-1 plus a `nondet` ahead of `ep`. Predicted pre-fix: T1 == zombie == 7, T2 == 4.
#[test]
fn nb_line18_witness_nondet() {
    arbitrate(prog_r2, "R-2", 7);
}

// -- Probe: diagnose the rejecting arm, the gate verdict, and ⊥-viability --------------------

use must::event::EventId;
use must::graph::ExecutionGraph;
use must::time::{check, gate_feasible};
use must::{consistent, traces_of, Observer};
use std::collections::{BTreeMap, VecDeque};

fn previous_set(g: &ExecutionGraph, e: EventId, porf_s: &BTreeSet<EventId>) -> BTreeSet<EventId> {
    let se = g.stamp(e);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) <= se || porf_s.contains(&x))
        .collect()
}
fn deleted_set(g: &ExecutionGraph, r: EventId, porf_s: &BTreeSet<EventId>) -> BTreeSet<EventId> {
    let sr = g.stamp(r);
    g.all_events()
        .into_iter()
        .filter(|&x| g.stamp(x) > sr && !porf_s.contains(&x))
        .collect()
}
/// `viability_base` reimplemented (revisit.rs): `Previous` minus the dependency cone of `ep`.
fn viability_base(g: &ExecutionGraph, ep: EventId, porf_s: &BTreeSet<EventId>) -> ExecutionGraph {
    let previous = previous_set(g, ep, porf_s);
    let n = g.num_threads();
    let mut diverge = vec![usize::MAX; n];
    diverge[ep.tid] = ep.idx + 1;
    loop {
        let mut changed = false;
        for &rp in &previous {
            if !g.label(rp).is_recv() {
                continue;
            }
            let Some(sp) = g.reads_from(rp) else { continue };
            if sp.idx >= diverge[sp.tid] && rp.idx < diverge[rp.tid] {
                diverge[rp.tid] = rp.idx;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let keep: BTreeSet<EventId> = previous
        .into_iter()
        .filter(|e| e.idx < diverge[e.tid])
        .collect();
    g.restrict(&keep)
}

/// Every consistent state reachable forward from `h0` (no revisits) — the independent
/// brute-force stand-in for `viable_search`'s DFS.
fn all_states<P: Program>(h0: &ExecutionGraph, program: &P) -> Vec<ExecutionGraph> {
    let n = program.num_threads();
    let mut seen: BTreeMap<String, ExecutionGraph> = BTreeMap::new();
    let mut queue: VecDeque<ExecutionGraph> = VecDeque::new();
    if consistent(h0) {
        seen.insert(h0.canonical_key(), h0.clone());
        queue.push_back(h0.clone());
    }
    while let Some(h) = queue.pop_front() {
        let traces = traces_of(&h, n);
        let nexts = program.next(&traces);
        for (tid, next) in nexts.iter().enumerate() {
            let ThreadNext::Next(label) = next else {
                continue;
            };
            let mut children: Vec<ExecutionGraph> = Vec::new();
            match label {
                Label::Send { .. } | Label::Error { .. } => {
                    let mut c = h.clone();
                    c.add_event(tid, label.clone());
                    children.push(c);
                }
                Label::Nondet { set } => {
                    for &v in set.iter() {
                        let mut c = h.clone();
                        let e = c.add_event(tid, label.clone());
                        c.set_nd(e, v);
                        children.push(c);
                    }
                }
                Label::Recv { .. } => {
                    let mut c = h.clone();
                    let e = c.add_event(tid, label.clone());
                    c.set_rf(e, None);
                    let mut opts: Vec<Option<EventId>> = c.iter_sends().map(Some).collect();
                    opts.push(None);
                    for src in opts {
                        let mut c2 = c.clone();
                        c2.set_rf(e, src);
                        children.push(c2);
                    }
                }
            }
            for c in children {
                if !consistent(&c) {
                    continue;
                }
                if let std::collections::btree_map::Entry::Vacant(slot) =
                    seen.entry(c.canonical_key())
                {
                    slot.insert(c.clone());
                    queue.push_back(c);
                }
            }
        }
    }
    seen.into_values().collect()
}

/// Brute-force viability of `base[ep ← src]` (`src == None` is the ⊥ option line 18 mandates):
/// does SOME forward completion witness `revisiting` present-unread, feasible and gate-passing?
#[allow(clippy::too_many_arguments)]
fn brute_viable<P: Program>(
    base: &ExecutionGraph,
    ep: EventId,
    src: Option<EventId>,
    program: &P,
    priorities: &[usize],
    revisiting: EventId,
    rev_label: &Label,
) -> bool {
    let mut h0 = base.clone();
    h0.set_rf(ep, src);
    all_states(&h0, program).iter().any(|h| {
        h.contains(revisiting)
            && h.label(revisiting) == rev_label
            && !h.is_read(revisiting)
            && check(h).is_feasible()
            && gate_feasible(h, program, priorities)
    })
}

struct Diagnose<MK, P: Program> {
    make: MK,
    _p: std::marker::PhantomData<P>,
}

impl<MK: Fn() -> P + Sync, P: Program> Observer for Diagnose<MK, P> {
    fn on_forced_closure_pruned(&self, g2: &ExecutionGraph, r: EventId, s: EventId) {
        eprintln!("--- revisit GATE-PRUNED (not the arm): r={r} <- s={s} {:?}", g2.all_events());
    }
    fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
        let porf_s = g.porf_prefix(s);
        let deleted = deleted_set(g, r, &porf_s);
        let p = (self.make)();
        let priorities: Vec<usize> = (0..p.num_threads()).collect();
        eprintln!("--- revisit rejected: r={r} <- s={s}   Deleted={deleted:?}");
        for ep in deleted.iter().copied().chain(std::iter::once(r)) {
            let lbl = g.label(ep).clone();
            if let Label::Recv {
                blocking: false, ..
            } = &lbl
            {
                if g.reads_bottom(ep) {
                    continue;
                }
                eprintln!(
                    "    ARM-18 FALSE at ep={ep} ({lbl:?}): reads {:?}",
                    g.reads_from(ep)
                );
                // Is ⊥ actually viable here? (the question line 18 never asks)
                let base = viability_base(g, ep, &porf_s);
                let rev_label = g.label(s).clone();
                let bot =
                    brute_viable(&base, ep, None, &p, &priorities, s, &rev_label);
                eprintln!("      bottom_viable={bot}  (false ⇒ line 18 is over-strict)");
                if let Some(held) = g.reads_from(ep) {
                    if base.thread_len(held.tid) > held.idx {
                        let v =
                            brute_viable(&base, ep, Some(held), &p, &priorities, s, &rev_label);
                        eprintln!("      held_viable({held})={v}");
                    }
                }
            }
        }
        // The two trap checks: the revisit really did reach the arm loop.
        let mut keep: BTreeSet<EventId> = g.all_events().into_iter().collect();
        for &d in &deleted {
            if d != s {
                keep.remove(&d);
            }
        }
        let mut g2 = g.restrict(&keep);
        g2.set_rf(r, Some(s));
        eprintln!(
            "    trap: consistent(g2)={} gate_feasible(g2)={} check(g2)={}",
            consistent(&g2),
            gate_feasible(&g2, &p, &priorities),
            check(&g2).is_feasible()
        );
    }
}

/// Diagnostic printout (not an assertion): every rejected revisit, the arm that rejected it, and
/// — for a line-18 rejection — whether ⊥ was actually viable. `bottom_viable=false` on the
/// canon-mandated ⊥ is the signature of the loss. Run with
/// `cargo test --release --test nb_line18 -- --ignored --nocapture`.
#[test]
#[ignore = "diagnostic printout, not an assertion"]
fn nb_line18_diagnose() {
    eprintln!("===== R-1 =====");
    explore(
        prog_r1,
        &Diagnose {
            make: prog_r1,
            _p: std::marker::PhantomData,
        },
        Config::default().collect_errors().with_time_predicate(),
    );
    eprintln!("===== R-2 =====");
    explore(
        prog_r2,
        &Diagnose {
            make: prog_r2,
            _p: std::marker::PhantomData,
        },
        Config::default().collect_errors().with_time_predicate(),
    );
}
