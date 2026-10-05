//! Eager-time realizability filter for terminal execution graphs (time-intervals extension,
//! phase T1).
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
//! # Monotonicity (documented, licenses forward pruning)
//!
//! Extending `G` only adds hard constraints and B-disjuncts (new sends = new competitors of
//! existing receives; A-clauses are unchanged), so an eager-infeasible prefix stays
//! infeasible. (The pruning it licenses lives in the explorer, not here.)
//!
//! # Model support (v1)
//!
//! Only Asyn and P2p carry time. [`eager_feasible`] takes a fast path (all windows untimed ⇒
//! realizable) *before* touching models, so every existing (untimed) oracle — including
//! cd/mbox — is unaffected; it panics only when a non-default window and a Cd/Mbox send are
//! both present. [`check`] always runs the full path and assumes Asyn/P2p (the guard is in
//! [`eager_feasible`]).

pub mod solver;

use std::collections::BTreeMap;
use std::fmt;

use crate::event::{EventId, Model};
use crate::graph::ExecutionGraph;
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

/// A satisfying eager schedule: arrival time of every send, fire time of every blocking
/// receive. All values are origin-anchored (`ORIGIN` = 0) and non-negative.
#[derive(Clone, Debug, Default)]
pub struct Schedule {
    pub arr: BTreeMap<EventId, i64>,
    pub fire: BTreeMap<EventId, i64>,
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

/// Whether `g` is eager-time-realizable. The filter the explorer applies to terminals.
///
/// Fast path: if every send window is untimed (`Window::ASAP`), `g` is realizable — returned
/// *before* any model check, so untimed graphs (any models) always pass and existing oracle
/// counts are unchanged. Panics only when a timed window and a Cd/Mbox send coexist (v1
/// supports Asyn/P2p only).
pub fn eager_feasible(g: &ExecutionGraph) -> bool {
    let any_timed = g
        .iter_sends()
        .any(|s| !g.send_window(s).map(|w| w.is_untimed()).unwrap_or(true));
    if !any_timed {
        return true; // fast path, ahead of the model guard
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
    check(g).is_feasible()
}

/// Full realizability check with a schedule / explanation. Always runs the complete path (no
/// fast path), so it is also the vacuity witness for untimed graphs. Assumes Asyn/P2p.
pub fn check(g: &ExecutionGraph) -> TimedVerdict {
    let builder = Builder::build(g);
    match solve(&builder.system) {
        Verdict::Sat { assignment } => TimedVerdict::Feasible(builder.schedule(&assignment)),
        Verdict::Unsat { cycle, .. } => TimedVerdict::Infeasible(builder.explanation(&cycle)),
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
        b.system.n_vars = b.vars.len() as u32;
        b
    }

    fn alloc(&mut self, v: TimeVar) -> VarId {
        let id = self.vars.len() as VarId;
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
    use crate::event::{Label, Model, Pred, Window};
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
}
