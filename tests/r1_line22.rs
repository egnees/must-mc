//! **R1 regression** (`C1_HARDENING_SPEC` §D.5, `R1_LINE22_SPEC`): the first machine-confirmed
//! completeness loss of T2, and the pinned witness that the existential line-22 canon fixes it.
//!
//! # The hole
//!
//! Before the fix, line 22 called a blocking receive canonical iff it read the
//! `(avail_lb, tid, idx)`-minimal source that was **locally** eager-feasible. Local feasibility
//! over-approximates viability, so the canon could name a source no completion realizes.
//!
//! Shape: `ep` (a blocking receive in `Deleted`) has two locally-feasible sources `s1`
//! (`avail` 10) and `s2` (`avail` 20). The `(avail, tid, idx)`-min is `s1` — but reading `s1`
//! makes T1 emit an early competitor `c` that kills T2's read of `m`, so the revisiting send `L`
//! exists **only** on the `s2` branch. The old arm therefore rejected the only holder that ever
//! reaches the revisit, the revisit fired from nowhere, and the terminal `r←L` was lost:
//! zombie/T1 found 3 realizable terminals, T2 found 2.
//!
//! This is the structural twin of the historical raft f1 28-vs-40 loss, which the *nondet* arm's
//! PASS rule already fixed; R1 is the same defect left standing on the *receive* arm.
//!
//! # Why the value-independent corpus could not find it
//!
//! The shape needs a blocking receive with **≥ 2 consistent sources of different completion
//! fate** in `G|_Previous`, which requires the read value to steer downstream emission — i.e.
//! value dependence. `fuzz_timed`'s 820 SeqProgram corpus is value-*independent*, so it is
//! structurally blind here, exactly as `TIME_PLAN` warned.
//!
//! # What is asserted
//!
//! Three-way arbitration on the witness: `realizable(T2) == realizable(zombie) ==
//! realizable(T1-filter)`, all three equal to 3 keys. Zombie and T1 are correct by construction
//! (untimed Algorithm 1 + the proven terminal filter), so the equality is a genuine certificate
//! for this program, not a self-consistency check.

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

fn keys(col: &ExecutionCollector) -> BTreeSet<String> {
    col.terminal_keys().into_iter().collect()
}

#[test]
fn r1_witness() {
    // T1-filter reference (untimed walk + post-hoc realizability filter).
    let t1c = ExecutionCollector::new();
    let t1n = CountingObserver::new();
    let obs = (t1c, t1n);
    explore(
        prog,
        &obs,
        Config::default().collect_errors().with_time_filter(),
    );
    let (t1c, t1n) = obs;
    let t1_keys = keys(&t1c);
    eprintln!(
        "T1-filter: full={} blocked={} filtered={} keys={}",
        t1n.full(),
        t1n.blocked(),
        t1n.filtered(),
        t1_keys.len()
    );
    for k in &t1_keys {
        eprintln!("  T1 {k}");
    }

    // Zombie (untimed Algorithm 1 under the DES order + the same filter).
    let zc = ExecutionCollector::new();
    explore(
        prog,
        &zc,
        Config::default().collect_errors().with_time_zombie(),
    );
    let z_keys = keys(&zc);
    eprintln!("zombie: keys={}", z_keys.len());
    assert_eq!(z_keys, t1_keys, "zombie must equal T1-filter");

    // T2 predicate.
    let t2c = ExecutionCollector::new();
    let t2n = CountingObserver::new();
    let obs = (t2c, t2n);
    explore(
        prog,
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let (t2c, t2n) = obs;
    let t2_keys = keys(&t2c);
    eprintln!(
        "T2-predicate: full={} blocked={} keys={}",
        t2n.full(),
        t2n.blocked(),
        t2_keys.len()
    );
    for k in &t2_keys {
        eprintln!("  T2 {k}");
    }
    for k in t1_keys.difference(&t2_keys) {
        eprintln!("  LOST BY T2: {k}");
    }
    for k in t2_keys.difference(&t1_keys) {
        eprintln!("  EXTRA IN T2: {k}");
    }
    assert_eq!(t2_keys, t1_keys, "R1: T2 lost a realizable terminal");
    // Pinned: the witness has exactly three realizable terminals. Before the R1 fix T2 reported
    // two of them. Do NOT relax this number — a change means the witness stopped exercising the
    // shape (see the module docs).
    assert_eq!(t1_keys.len(), 3, "witness must have 3 realizable terminals");
}

// -- Probe 2: diagnose the rejecting arm and the two candidate verdicts ----------------------

use must::event::EventId;
use must::explorer::revisit::get_cons_tiebreaker;
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
/// `viability_base` reimplemented (revisit.rs:219): Previous minus the dependency cone of `ep`.
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
            let ThreadNext::Next(label) = next else { continue };
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

/// Brute-force `viable_recv`: ∃ a reachable state from `base[ep←src]` with `revisiting`
/// present-unread, feasible and gate-passing.
fn brute_viable_recv<P: Program>(
    base: &ExecutionGraph,
    ep: EventId,
    src: EventId,
    program: &P,
    priorities: &[usize],
    revisiting: EventId,
    rev_label: &Label,
) -> bool {
    let mut h0 = base.clone();
    h0.set_rf(ep, Some(src));
    all_states(&h0, program).iter().any(|h| {
        h.contains(revisiting)
            && h.label(revisiting) == rev_label
            && !h.is_read(revisiting)
            && check(h).is_feasible()
            && gate_feasible(h, program, priorities)
    })
}

struct Diagnose;

impl Observer for Diagnose {
    fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
        let porf_s = g.porf_prefix(s);
        let deleted = deleted_set(g, r, &porf_s);
        let p = prog();
        let priorities: Vec<usize> = (0..p.num_threads()).collect();
        eprintln!("--- revisit rejected: r={r} <- s={s}");
        for ep in deleted.iter().copied().chain(std::iter::once(r)) {
            let lbl = g.label(ep).clone();
            let ok = match &lbl {
                Label::Recv { blocking: false, .. } => g.reads_bottom(ep),
                Label::Recv { blocking: true, .. } => {
                    let prev = previous_set(g, ep, &porf_s);
                    let h = g.restrict(&prev);
                    let tb = get_cons_tiebreaker(&h, ep, true);
                    let held = g.reads_from(ep);
                    if tb != held {
                        eprintln!(
                            "    ARM-22 FALSE at ep={ep} ({lbl:?}): held={held:?} tiebreaker={tb:?}"
                        );
                        // Which candidates are locally feasible, and are they viable?
                        let base = viability_base(g, ep, &porf_s);
                        let rev_label = g.label(s).clone();
                        for cand in h.sends() {
                            if !h.matches(cand, ep) {
                                continue;
                            }
                            let mut hp = h.clone();
                            hp.set_rf(ep, None);
                            let read_by_other = hp
                                .recvs()
                                .into_iter()
                                .any(|rp| rp != ep && hp.reads_from(rp) == Some(cand));
                            if read_by_other {
                                continue;
                            }
                            let mut trial = hp.clone();
                            trial.set_rf(ep, Some(cand));
                            let cons = consistent(&trial);
                            let feas = cons && check(&trial).is_feasible();
                            let viab = base.contains(cand)
                                && brute_viable_recv(
                                    &base, ep, cand, &p, &priorities, s, &rev_label,
                                );
                            eprintln!(
                                "      cand={cand} local_cons={cons} local_feas={feas} \
                                 brute_viable={viab}"
                            );
                        }
                    }
                    tb == held
                }
                Label::Nondet { set } => {
                    let min = set.iter().min_by(|a, b| {
                        must::intern::resolve(**a).cmp(must::intern::resolve(**b))
                    });
                    g.nd_value(ep) == min
                }
                Label::Send { .. } | Label::Error { .. } => {
                    let prev = previous_set(g, ep, &porf_s);
                    !prev
                        .iter()
                        .any(|&rp| g.label(rp).is_recv() && g.reads_from(rp) == Some(ep))
                }
            };
            if !ok {
                eprintln!("    arm FALSE at {ep} {lbl:?}");
            }
        }
    }
}

/// Diagnostic, not an assertion: prints every rejected revisit with the arm that rejected it and,
/// for a blocking-receive arm, each candidate source with its local consistency, local
/// feasibility and **brute-force** viability. This is what localized R1 in the first place —
/// `local_feas=true, brute_viable=false` on the canon-chosen source is the signature. Run with
/// `cargo test --release --test r1_line22 -- --ignored --nocapture`.
#[test]
#[ignore = "diagnostic printout, not an assertion"]
fn r1_diagnose() {
    explore(
        prog,
        &Diagnose,
        Config::default().collect_errors().with_time_predicate(),
    );
}
