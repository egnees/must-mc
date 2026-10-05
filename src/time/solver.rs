//! Incremental difference-constraint solver with a disjunctive (DPLL) layer.
//!
//! The time filter reduces "is this terminal graph time-realizable?" to the feasibility of
//! a system of difference constraints `x - y <= w` (Cotton–Maler, SAT 2006) plus a handful
//! of binary/n-ary disjunctions (one per blocking receive and per multi-send p2p channel
//! prefix; see [`crate::time`] and engine_plan §0/§4.1). This module is the abstract core:
//! it knows nothing about graphs, only variables, edges and clauses.
//!
//! # Conventions (fixed once, used everywhere)
//!
//! * An [`Edge`] `{x, y, w}` is the constraint `x - y <= w`. `∞` (no constraint) is simply
//!   the absence of an edge — there are no sentinel weights.
//! * In graph terms a constraint `x - y <= w` is the arc `y ─w→ x` (tail `y`, head `x`);
//!   feasibility ⟺ that arc graph has no negative cycle. A valid potential `π` keeps every
//!   arc's reduced weight `π[tail] + w − π[head] ≥ 0`, and then `x_i = π[i]` is a feasible
//!   assignment. [`PotentialCore`] maintains such a `π` incrementally.
//! * [`ORIGIN`] is variable 0. Assignments are reported anchored at the origin
//!   (`model[i] = π[i] − π[ORIGIN]`, so `model[ORIGIN] = 0`); the builder in
//!   [`crate::time`] adds `v ≥ ORIGIN` edges for every time variable, which pins the origin
//!   to time 0 and makes the reported schedule the pointwise-earliest one.
//!
//! # Overflow invariant
//!
//! Every weight is a finite window bound, `|w| ≤ Window::MAX_BOUND = 2^40`. A potential (or
//! Bellman–Ford distance) is a sum of at most `|E|` such weights, so `|π[i]| ≤ |E| · 2^40`,
//! which stays well inside `i64` for any graph the explorer can build. All arithmetic is
//! plain `i64`; no saturating/checked ops are needed.
//!
//! Determinism: only `Vec`/`BTreeMap`; the propagation heap breaks ties by variable id.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

/// Difference-constraint variable. Variable [`ORIGIN`] is reserved.
pub type VarId = u32;

/// The origin variable, fixed at time 0 (see the module docs).
pub const ORIGIN: VarId = 0;

/// The constraint `x - y <= w`. Its absence encodes `∞` (no bound); there is no sentinel.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Edge {
    pub x: VarId,
    pub y: VarId,
    pub w: i64,
}

/// A disjunction of conjunctions: the clause holds iff *some* alternative `alts[k]` holds,
/// where an alternative is the conjunction of its edges. A binary A/B receive clause and an
/// n-ary "max" clause are both this shape (engine_plan §4.2).
#[derive(Clone, Debug)]
pub struct Clause {
    pub alts: Vec<Vec<Edge>>,
}

/// A constraint system: `hard` edges that always hold, plus `clauses` (disjunctions).
#[derive(Clone, Debug, Default)]
pub struct System {
    pub n_vars: u32,
    pub hard: Vec<Edge>,
    pub clauses: Vec<Clause>,
}

/// Result of [`solve`]. `Sat` carries a satisfying assignment (one `i64` per variable,
/// origin-anchored). `Unsat` carries a witness negative `cycle` and the `choices`
/// `(clause_idx, alt_idx)` in force when it was found — a certificate of one infeasible
/// combination, not a full refutation proof.
#[derive(Clone, Debug)]
pub enum Verdict {
    Sat {
        assignment: Vec<i64>,
    },
    Unsat {
        cycle: Vec<Edge>,
        choices: Vec<(usize, usize)>,
    },
}

impl Verdict {
    pub fn is_sat(&self) -> bool {
        matches!(self, Verdict::Sat { .. })
    }
}

/// A negative cycle discovered by [`DiffCore::assert_edge`]: the (minimal) set of edges whose
/// weights sum to a negative loop, i.e. an unsatisfiable core of the current edge set.
#[derive(Clone, Debug)]
pub struct Conflict {
    pub cycle: Vec<Edge>,
}

/// Incremental difference-constraint core: assert edges, checkpoint/rollback, read a model.
///
/// `assert_edge` returns `Err(Conflict)` exactly when the new edge closes a negative cycle;
/// on `Err` the edge stays recorded (so a following [`pop`](Self::pop) removes it) but the
/// core's internal feasibility witness is left valid. `push`/`pop` are a nesting stack of
/// checkpoints; `pop` removes edges added since the matching `push` and, per Cotton–Maler,
/// deliberately does *not* restore the potential (a valid potential stays valid after edges
/// are dropped — only its minimality is lost).
pub trait DiffCore {
    fn new(n_vars: u32) -> Self;
    fn assert_edge(&mut self, e: Edge) -> Result<(), Conflict>;
    fn push(&mut self);
    fn pop(&mut self);
    /// A satisfying assignment for the edges asserted so far, anchored so `model[ORIGIN] = 0`.
    fn model(&self) -> Vec<i64>;
}

const NO_REASON: usize = usize::MAX;

/// Cotton–Maler potential core (research.md "Эскиз ядра"). Maintains a valid potential `π`;
/// inserting an edge with negative reduced slack triggers a Dijkstra-like relaxation over
/// non-negative reduced weights that either restores `π` or, on returning to the inserted
/// edge's tail, reports the negative cycle it closed.
pub struct PotentialCore {
    /// Valid potential: `pot[tail] + w − pot[head] ≥ 0` on every recorded arc.
    pot: Vec<i64>,
    /// Adjacency by graph tail: `out[y]` holds `(head, w, edge_id)` for each arc `y ─w→ head`.
    out: Vec<Vec<(VarId, i64, usize)>>,
    /// Every asserted edge by id (insertion order); backs cycle recovery and rollback.
    edges: Vec<Edge>,
    /// Checkpoint stack: each entry is `edges.len()` at a [`push`](Self::push).
    checkpoints: Vec<usize>,
    // --- reusable propagation scratch (reset via `dirty` after each assert) ---
    /// `gamma[v] < 0` is the pending decrement of `pot[v]`; `0` means "untouched".
    gamma: Vec<i64>,
    /// `reason[v]` is the arc that set `gamma[v]` (its head is `v`); used to recover a cycle.
    reason: Vec<usize>,
    /// Whether `v` has been finalized (potential committed) in this propagation.
    finalized: Vec<bool>,
    /// Variables touched this propagation, to reset `gamma`/`reason`/`finalized` cheaply.
    dirty: Vec<VarId>,
    /// Min-heap on `(gamma, VarId)`: pops the most-negative gamma first, ties by smallest id.
    heap: BinaryHeap<(Reverse<i64>, Reverse<VarId>)>,
}

impl PotentialCore {
    #[inline]
    fn mark_dirty(&mut self, v: VarId) {
        self.dirty.push(v);
    }

    /// Reset the propagation scratch touched this round back to its idle state.
    fn reset_scratch(&mut self) {
        for &v in &self.dirty {
            let i = v as usize;
            self.gamma[i] = 0;
            self.reason[i] = NO_REASON;
            self.finalized[i] = false;
        }
        self.dirty.clear();
        self.heap.clear();
    }

    /// Walk `reason` pointers from the inserted edge's tail back to its head, collecting the
    /// arcs of the negative cycle (the inserted arc `tail ─→ head` plus the path
    /// `head ─→ … ─→ tail`). See the module conventions for the arc/edge correspondence.
    fn recover_cycle(&self, tail: VarId, _head: VarId) -> Vec<Edge> {
        let mut cyc = Vec::new();
        let mut v = tail;
        // At most `edges.len()` steps: `reason` forms a tree, so this terminates.
        for _ in 0..=self.edges.len() {
            let eid = self.reason[v as usize];
            debug_assert!(eid != NO_REASON, "cycle recovery hit an unset reason");
            let e = self.edges[eid];
            cyc.push(e);
            let pred = e.y; // the arc's graph tail = the predecessor of `v`
            if pred == tail {
                break;
            }
            v = pred;
        }
        cyc
    }
}

impl DiffCore for PotentialCore {
    fn new(n_vars: u32) -> Self {
        let n = n_vars as usize;
        PotentialCore {
            pot: vec![0; n],
            out: vec![Vec::new(); n],
            edges: Vec::new(),
            checkpoints: Vec::new(),
            gamma: vec![0; n],
            reason: vec![NO_REASON; n],
            finalized: vec![false; n],
            dirty: Vec::new(),
            heap: BinaryHeap::new(),
        }
    }

    fn assert_edge(&mut self, e: Edge) -> Result<(), Conflict> {
        let id = self.edges.len();
        self.edges.push(e);
        self.out[e.y as usize].push((e.x, e.w, id));

        // Self-loop `x - x <= w` is `0 <= w`: a no-op if `w >= 0`, an immediate negative
        // cycle otherwise (the general propagation assumes tail != head).
        if e.x == e.y {
            return if e.w >= 0 {
                Ok(())
            } else {
                Err(Conflict { cycle: vec![e] })
            };
        }

        let head = e.x;
        let tail = e.y;
        let slack = self.pot[tail as usize] + e.w - self.pot[head as usize];
        if slack >= 0 {
            return Ok(()); // fast path: potential already valid for the new arc
        }

        // Lower `pot[head]` by `slack` and cascade the decrement along out-arcs. Vertices
        // are finalized in order of most-negative gamma (largest decrement) first.
        self.gamma[head as usize] = slack;
        self.reason[head as usize] = id;
        self.mark_dirty(head);
        self.heap.push((Reverse(slack), Reverse(head)));

        // Potential decrements committed this round, for rollback if a cycle is found.
        let mut committed: Vec<(VarId, i64)> = Vec::new();
        let mut cycle_found = false;

        while let Some((Reverse(g), Reverse(s))) = self.heap.pop() {
            if self.finalized[s as usize] || g > self.gamma[s as usize] {
                continue; // stale heap entry
            }
            let delta = self.gamma[s as usize];
            self.pot[s as usize] += delta;
            committed.push((s, delta));
            self.finalized[s as usize] = true;

            // Iterate out[s] by index: we mutate `self` (gamma/pot/heap) inside the loop.
            let deg = self.out[s as usize].len();
            for k in 0..deg {
                let (t, c, eid) = self.out[s as usize][k];
                if self.finalized[t as usize] {
                    continue;
                }
                let d = self.pot[s as usize] + c - self.pot[t as usize];
                if d < self.gamma[t as usize] {
                    if t == tail {
                        // Reached the inserted edge's tail: a negative cycle through it.
                        self.reason[tail as usize] = eid;
                        self.mark_dirty(tail);
                        cycle_found = true;
                        break;
                    }
                    self.gamma[t as usize] = d;
                    self.reason[t as usize] = eid;
                    self.mark_dirty(t);
                    self.heap.push((Reverse(d), Reverse(t)));
                }
            }
            if cycle_found {
                break;
            }
        }

        if cycle_found {
            // Undo this round's partial potential changes so `π` stays valid for the edge
            // set minus the offending arc (which remains recorded until the caller pops).
            for &(v, delta) in &committed {
                self.pot[v as usize] -= delta;
            }
            let cyc = self.recover_cycle(tail, head);
            self.reset_scratch();
            Err(Conflict { cycle: cyc })
        } else {
            self.reset_scratch();
            Ok(()) // π' is valid (Cotton–Maler)
        }
    }

    fn push(&mut self) {
        self.checkpoints.push(self.edges.len());
    }

    fn pop(&mut self) {
        let cp = self.checkpoints.pop().expect("pop without matching push");
        while self.edges.len() > cp {
            let e = self.edges.pop().unwrap();
            // The last arc recorded with tail `e.y` is exactly this edge (edges are popped
            // in reverse insertion order), so a plain `pop` removes the right one.
            self.out[e.y as usize].pop();
        }
        // Potential is intentionally left untouched (still valid for the smaller edge set).
    }

    fn model(&self) -> Vec<i64> {
        let anchor = self.pot[ORIGIN as usize];
        self.pot.iter().map(|&p| p - anchor).collect()
    }
}

/// Plain Bellman–Ford reference core, used only to cross-check [`PotentialCore`]'s verdicts
/// in tests. `O(V·E)` per assert — never on the hot path.
pub struct BellmanFordCore {
    n: usize,
    edges: Vec<Edge>,
    checkpoints: Vec<usize>,
}

impl BellmanFordCore {
    /// Bellman–Ford over the current edges (arc `y ─w→ x`, relaxing `x <= y + w`) from an
    /// implicit all-zero source. Returns a negative cycle's edges if one exists.
    fn find_negative_cycle(&self) -> Option<Vec<Edge>> {
        let n = self.n;
        if n == 0 {
            return None;
        }
        let mut dist = vec![0i64; n];
        let mut pred_edge = vec![NO_REASON; n];
        for iter in 0..n {
            let mut changed: Option<usize> = None;
            for (id, e) in self.edges.iter().enumerate() {
                let (y, x, w) = (e.y as usize, e.x as usize, e.w);
                if dist[y] + w < dist[x] {
                    dist[x] = dist[y] + w;
                    pred_edge[x] = id;
                    changed = Some(x);
                }
            }
            match changed {
                None => return None, // fixpoint reached before round n: feasible
                Some(x) if iter == n - 1 => {
                    // Still relaxing on round n: a negative cycle is reachable from `x`.
                    let mut v = x;
                    for _ in 0..n {
                        v = self.edges[pred_edge[v]].y as usize;
                    }
                    let start = v;
                    let mut cyc = Vec::new();
                    loop {
                        let eid = pred_edge[v];
                        cyc.push(self.edges[eid]);
                        v = self.edges[eid].y as usize;
                        if v == start {
                            break;
                        }
                    }
                    cyc.reverse();
                    return Some(cyc);
                }
                Some(_) => {}
            }
        }
        None
    }
}

impl DiffCore for BellmanFordCore {
    fn new(n_vars: u32) -> Self {
        BellmanFordCore {
            n: n_vars as usize,
            edges: Vec::new(),
            checkpoints: Vec::new(),
        }
    }

    fn assert_edge(&mut self, e: Edge) -> Result<(), Conflict> {
        self.edges.push(e); // stays recorded on conflict, mirroring PotentialCore
        match self.find_negative_cycle() {
            Some(cycle) => Err(Conflict { cycle }),
            None => Ok(()),
        }
    }

    fn push(&mut self) {
        self.checkpoints.push(self.edges.len());
    }

    fn pop(&mut self) {
        let cp = self.checkpoints.pop().expect("pop without matching push");
        self.edges.truncate(cp);
    }

    fn model(&self) -> Vec<i64> {
        let n = self.n;
        let mut dist = vec![0i64; n];
        for _ in 0..n {
            let mut changed = false;
            for e in &self.edges {
                let (y, x, w) = (e.y as usize, e.x as usize, e.w);
                if dist[y] + w < dist[x] {
                    dist[x] = dist[y] + w;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let anchor = dist[ORIGIN as usize];
        dist.iter().map(|&d| d - anchor).collect()
    }
}

/// Solve `sys` with [`PotentialCore`]. See [`solve_with`].
pub fn solve(sys: &System) -> Verdict {
    solve_with::<PotentialCore>(sys)
}

/// Solve `sys` with the given [`DiffCore`]: assert the hard edges, then a DPLL search over
/// the clauses (unit propagation by forward checking + chronological branching + semantic
/// branching on binary single-edge alternatives; research.md "Дизъюнкционный слой").
pub fn solve_with<C: DiffCore>(sys: &System) -> Verdict {
    let mut d = Dpll {
        core: C::new(sys.n_vars),
        sys,
        chosen: vec![None; sys.clauses.len()],
        stack: Vec::new(),
        witness_cycle: Vec::new(),
        witness_choices: Vec::new(),
    };
    for &e in &sys.hard {
        if let Err(c) = d.core.assert_edge(e) {
            return Verdict::Unsat {
                cycle: c.cycle,
                choices: Vec::new(),
            };
        }
    }
    if d.search() {
        Verdict::Sat {
            assignment: d.core.model(),
        }
    } else {
        Verdict::Unsat {
            cycle: d.witness_cycle,
            choices: d.witness_choices,
        }
    }
}

/// DPLL search state over the disjunctive layer.
struct Dpll<'a, C: DiffCore> {
    core: C,
    sys: &'a System,
    /// `chosen[j] = Some(a)` once clause `j` is committed to alternative `a`.
    chosen: Vec<Option<usize>>,
    /// Current decision stack `(clause_idx, alt_idx)`, for the unsat witness.
    stack: Vec<(usize, usize)>,
    witness_cycle: Vec<Edge>,
    witness_choices: Vec<(usize, usize)>,
}

impl<C: DiffCore> Dpll<'_, C> {
    /// Assert every edge of `alt` (stopping at the first conflict), recording an unsat
    /// witness on conflict. Caller manages the surrounding `push`/`pop`.
    fn assert_alt(&mut self, alt: &[Edge]) -> bool {
        for &e in alt {
            if let Err(c) = self.core.assert_edge(e) {
                self.witness_cycle = c.cycle;
                self.witness_choices = self.stack.clone();
                return false;
            }
        }
        true
    }

    /// Whether `alt` can be added on top of the current state without a conflict. Probes
    /// under a checkpoint and rolls back, leaving the core logically unchanged.
    fn probe_alt(&mut self, alt: &[Edge]) -> bool {
        self.core.push();
        let ok = self.assert_alt(alt);
        self.core.pop();
        ok
    }

    /// Semantic branching: on the B alternative (`a == 1`) of a binary clause whose A
    /// alternative is a single edge, additionally assert `¬A`. For integers,
    /// `¬(x − y <= w)` is `y − x <= −w − 1` — one edge (research.md).
    fn maybe_semantic(&mut self, j: usize, a: usize) -> bool {
        let alts = &self.sys.clauses[j].alts;
        if a == 1 && alts.len() == 2 && alts[0].len() == 1 {
            let g = alts[0][0];
            let neg = Edge {
                x: g.y,
                y: g.x,
                w: -g.w - 1,
            };
            return self.assert_alt(&[neg]);
        }
        true
    }

    /// DPLL. Returns `true` leaving the core in a satisfying state; `false` after undoing
    /// every edge it asserted at this level and resetting the clauses it forced.
    fn search(&mut self) -> bool {
        self.core.push();
        let mut forced: Vec<usize> = Vec::new();

        // Unit propagation by forward checking: force any clause with a single live alt.
        loop {
            let mut progress = false;
            for j in 0..self.sys.clauses.len() {
                if self.chosen[j].is_some() {
                    continue;
                }
                let n_alts = self.sys.clauses[j].alts.len();
                let mut alive: Option<usize> = None;
                let mut count = 0;
                for a in 0..n_alts {
                    let alt = self.sys.clauses[j].alts[a].clone();
                    if self.probe_alt(&alt) {
                        count += 1;
                        alive = Some(a);
                        if count > 1 {
                            break;
                        }
                    }
                }
                if count == 0 {
                    // No alternative survives: this branch is dead.
                    for &c in &forced {
                        self.chosen[c] = None;
                    }
                    self.core.pop();
                    return false;
                }
                if count == 1 {
                    let a = alive.unwrap();
                    let alt = self.sys.clauses[j].alts[a].clone();
                    let ok = self.assert_alt(&alt); // probed safe on this exact state
                    debug_assert!(ok, "forced alternative conflicted after probing clean");
                    let _ = ok;
                    self.chosen[j] = Some(a);
                    forced.push(j);
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }

        // Branch on the first still-open clause, alternatives in index order.
        let open = (0..self.sys.clauses.len()).find(|&j| self.chosen[j].is_none());
        match open {
            None => true, // all clauses satisfied: leave the core in its satisfying state
            Some(j) => {
                let n_alts = self.sys.clauses[j].alts.len();
                for a in 0..n_alts {
                    self.core.push();
                    self.stack.push((j, a));
                    let alt = self.sys.clauses[j].alts[a].clone();
                    let ok = self.assert_alt(&alt) && self.maybe_semantic(j, a);
                    if ok {
                        self.chosen[j] = Some(a);
                        if self.search() {
                            return true;
                        }
                        self.chosen[j] = None;
                    }
                    self.stack.pop();
                    self.core.pop();
                }
                for &c in &forced {
                    self.chosen[c] = None;
                }
                self.core.pop();
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // "a >= b + k" as an edge (b - a <= -k).
    fn ge(a: VarId, b: VarId, k: i64) -> Edge {
        Edge { x: b, y: a, w: -k }
    }
    // "a <= b + k" as an edge (a - b <= k).
    fn le(a: VarId, b: VarId, k: i64) -> Edge {
        Edge { x: a, y: b, w: k }
    }

    /// SplitMix64 (copied from tests/fuzz.rs) for reproducible cross-check systems.
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

    fn assignment(v: &Verdict) -> &[i64] {
        match v {
            Verdict::Sat { assignment } => assignment,
            Verdict::Unsat { .. } => panic!("expected Sat, got {v:?}"),
        }
    }

    #[test]
    fn feasible_chain() {
        // ORIGIN=0, x1=1, x2=2 with x1 >= x0 + 5, x2 >= x1 + 5.
        let sys = System {
            n_vars: 3,
            hard: vec![ge(1, ORIGIN, 5), ge(2, 1, 5)],
            clauses: vec![],
        };
        let v = solve(&sys);
        assert!(v.is_sat());
        // Earliest schedule, origin-anchored.
        assert_eq!(assignment(&v), &[0, 5, 10]);
    }

    #[test]
    fn negative_cycle_exact_certificate() {
        // x1 >= x0 + 1 and x0 >= x1 + 1: a two-edge negative cycle.
        let e_up = ge(1, ORIGIN, 1); // Edge{x:0, y:1, w:-1}
        let e_dn = ge(ORIGIN, 1, 1); // Edge{x:1, y:0, w:-1}
        let sys = System {
            n_vars: 2,
            hard: vec![e_up, e_dn],
            clauses: vec![],
        };
        match solve(&sys) {
            Verdict::Unsat { cycle, choices } => {
                assert!(choices.is_empty(), "hard conflict has no choices");
                // The certificate is exactly the two edges of the cycle (as a set).
                assert_eq!(cycle.len(), 2);
                assert!(cycle.contains(&e_up));
                assert!(cycle.contains(&e_dn));
            }
            v => panic!("expected Unsat, got {v:?}"),
        }
    }

    #[test]
    fn unit_propagation_forces_alternative() {
        // Hard: x1 >= x0 + 5. Clause: (x1 <= x0)  OR  (x1 >= x0 + 10).
        // The first alt is dead (contradicts the hard edge), so the second is forced.
        let sys = System {
            n_vars: 2,
            hard: vec![ge(1, ORIGIN, 5)],
            clauses: vec![Clause {
                alts: vec![vec![le(1, ORIGIN, 0)], vec![ge(1, ORIGIN, 10)]],
            }],
        };
        let v = solve(&sys);
        assert!(v.is_sat());
        // Forced into x1 >= x0 + 10, so the earliest x1 is 10, not 5.
        assert_eq!(assignment(&v), &[0, 10]);
    }

    #[test]
    fn two_disjunctions_four_leaves() {
        // Two independent binary clauses over x1, x2, both satisfiable in some branch.
        // Clause A: x1 <= x0     OR x1 >= x0 + 4
        // Clause B: x2 <= x1     OR x2 >= x1 + 4
        let mk = |a_low_first: bool, b_low_first: bool| {
            // Each clause has two single-edge alternatives; the flags just swap their order,
            // exercising branch order independence (all four leaves are satisfiable).
            let a = if a_low_first {
                vec![vec![le(1, ORIGIN, 0)], vec![ge(1, ORIGIN, 4)]]
            } else {
                vec![vec![ge(1, ORIGIN, 4)], vec![le(1, ORIGIN, 0)]]
            };
            let b = if b_low_first {
                vec![vec![le(2, 1, 0)], vec![ge(2, 1, 4)]]
            } else {
                vec![vec![ge(2, 1, 4)], vec![le(2, 1, 0)]]
            };
            System {
                n_vars: 3,
                hard: vec![],
                clauses: vec![Clause { alts: a }, Clause { alts: b }],
            }
        };
        // All four alternative orderings are individually satisfiable.
        for &(x, y) in &[(true, true), (true, false), (false, true), (false, false)] {
            assert!(solve(&mk(x, y)).is_sat());
        }

        // Now make both clauses jointly force a contradiction with a hard edge:
        // hard x1 == x0 (both bounds) rules out (x1 >= x0 + 4); if the only alts are
        // the "high" ones, the system is unsat.
        let sys = System {
            n_vars: 2,
            hard: vec![le(1, ORIGIN, 0), ge(1, ORIGIN, 0)],
            clauses: vec![Clause {
                alts: vec![vec![ge(1, ORIGIN, 4)]],
            }],
        };
        assert!(!solve(&sys).is_sat());
    }

    #[test]
    fn nary_max_clause() {
        // Avail = max(Arr0, Arr1, Arr2): hard Avail >= each, plus a 3-ary clause forcing
        // Avail <= one of them (so equality with the largest is the only feasible pick).
        // Vars: 0=ORIGIN, 1=avail, 2=arr0, 3=arr1, 4=arr2. Pin arrs to 3, 7, 5.
        let av = 1;
        let (a0, a1, a2) = (2, 3, 4);
        let mut hard = vec![
            le(a0, ORIGIN, 3),
            ge(a0, ORIGIN, 3),
            le(a1, ORIGIN, 7),
            ge(a1, ORIGIN, 7),
            le(a2, ORIGIN, 5),
            ge(a2, ORIGIN, 5),
            ge(av, a0, 0),
            ge(av, a1, 0),
            ge(av, a2, 0),
        ];
        // Origin lower bounds (mirroring the builder) so the schedule is non-negative.
        for v in 1..=4 {
            hard.push(ge(v, ORIGIN, 0));
        }
        let sys = System {
            n_vars: 5,
            hard,
            clauses: vec![Clause {
                alts: vec![
                    vec![le(av, a0, 0)],
                    vec![le(av, a1, 0)],
                    vec![le(av, a2, 0)],
                ],
            }],
        };
        let v = solve(&sys);
        assert!(v.is_sat());
        // max(3,7,5) = 7.
        assert_eq!(assignment(&v)[av as usize], 7);
    }

    #[test]
    fn equalities_pin_a_value() {
        // A pair of edges x1 <= x0 + 3 and x1 >= x0 + 3 pins x1 = x0 + 3.
        let sys = System {
            n_vars: 2,
            hard: vec![le(1, ORIGIN, 3), ge(1, ORIGIN, 3)],
            clauses: vec![],
        };
        let v = solve(&sys);
        assert!(v.is_sat());
        assert_eq!(assignment(&v), &[0, 3]);
    }

    /// Build a small random system for the two-core cross-check.
    fn random_system(rng: &mut Rng) -> System {
        let n_vars = 2 + rng.below(4); // 2..=5 variables
        let n_hard = rng.below(6); // 0..=5 hard edges
        let mut hard = Vec::new();
        for _ in 0..n_hard {
            let x = rng.below(n_vars) as VarId;
            let y = rng.below(n_vars) as VarId;
            let w = rng.below(7) as i64 - 3; // -3..=3
            hard.push(Edge { x, y, w });
        }
        let n_clauses = rng.below(3); // 0..=2 clauses
        let mut clauses = Vec::new();
        for _ in 0..n_clauses {
            let n_alts = 1 + rng.below(3); // 1..=3 alternatives
            let mut alts = Vec::new();
            for _ in 0..n_alts {
                let n_edges = 1 + rng.below(2); // 1..=2 edges
                let mut es = Vec::new();
                for _ in 0..n_edges {
                    let x = rng.below(n_vars) as VarId;
                    let y = rng.below(n_vars) as VarId;
                    let w = rng.below(7) as i64 - 3;
                    es.push(Edge { x, y, w });
                }
                alts.push(es);
            }
            clauses.push(Clause { alts });
        }
        System {
            n_vars: n_vars as u32,
            hard,
            clauses,
        }
    }

    #[test]
    fn potential_matches_bellman_ford_on_random_systems() {
        let mut rng = Rng::new(0xC0FF_EE12_3456_789A);
        for _ in 0..200 {
            let sys = random_system(&mut rng);
            let vp = solve_with::<PotentialCore>(&sys);
            let vb = solve_with::<BellmanFordCore>(&sys);
            assert_eq!(
                vp.is_sat(),
                vb.is_sat(),
                "cores disagree on {sys:?}: potential={vp:?} bellman-ford={vb:?}"
            );
            // A reported Sat assignment must actually satisfy the hard edges.
            if let Verdict::Sat { assignment } = &vp {
                for e in &sys.hard {
                    let lhs = assignment[e.x as usize] - assignment[e.y as usize];
                    assert!(
                        lhs <= e.w,
                        "assignment violates hard edge {e:?}: {lhs} > {}",
                        e.w
                    );
                }
            }
        }
    }
}
