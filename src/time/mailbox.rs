//! Direct mailbox-delivery semantics for Asyn, P2p and Mbox.
//!
//! Every completed receive advances its process clock. Timeout windows bound empty
//! completion, and only their upper bound limits eager success; polling windows bound
//! both outcomes. Physical ties are nondeterministic subject to action causality.
//! Pure Asyn uses physical variables alone (ASYN_AND_TIMED_RECEIVES §7). P2p and
//! Mbox additionally use action ranks, which express order without a physical epsilon.
//!
//! Mbox witnesses a single global order of actual send operations. Deliveries to one
//! destination follow that order; different destinations may deliver independently.
//! Matching queued Mbox sources obey that same order. This is the physical refinement
//! of MUST's existential send order, not an Asyn fallback or a global delivery FIFO.
//!
//! Use these entry points explicitly for send-only graphs and closed restrictions that
//! have lost all receive annotations. An abstract nonblocking receive and Cd are rejected
//! explicitly; neither has an implicit interpretation in this mode.

use std::collections::{BTreeMap, BTreeSet};

use crate::consistency::consistent;
use crate::event::{EventId, Label, Model, ReceiveTiming, Window};
use crate::graph::ExecutionGraph;

use super::solver::{solve, Clause, Edge, System, VarId, Verdict, ORIGIN};
use super::{Earliest, ExplainAtom, Explanation, Schedule, TimedVerdict};

/// An auxiliary physical action. These are witness data, not outer MUST vertices.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action {
    Send(EventId),
    Deliver(EventId),
    Invoke(EventId),
    Complete(EventId),
    Local(EventId),
}

impl Action {
    /// Discriminant index, **in declaration order** — which is also `Ord` order, so
    /// iterating `kind`-major and then by dense event index reproduces exactly the order a
    /// `BTreeMap<Action, _>` yields. [`Builder`] relies on that to keep witness extraction
    /// byte-identical after the side maps became dense arrays.
    #[inline]
    fn kind(self) -> usize {
        match self {
            Action::Send(_) => 0,
            Action::Deliver(_) => 1,
            Action::Invoke(_) => 2,
            Action::Complete(_) => 3,
            Action::Local(_) => 4,
        }
    }

    #[inline]
    fn event(self) -> EventId {
        match self {
            Action::Send(e)
            | Action::Deliver(e)
            | Action::Invoke(e)
            | Action::Complete(e)
            | Action::Local(e) => e,
        }
    }

    #[inline]
    fn of_kind(kind: usize, e: EventId) -> Action {
        match kind {
            0 => Action::Send(e),
            1 => Action::Deliver(e),
            2 => Action::Invoke(e),
            3 => Action::Complete(e),
            _ => Action::Local(e),
        }
    }
}

/// Number of [`Action`] kinds; the action tables are `KINDS * n_events` long.
const KINDS: usize = 5;

/// "No variable" sentinel for the dense tables (a real [`VarId`] is `< n_vars`).
const NO_VAR: VarId = VarId::MAX;

/// One action in a schedule. The enclosing vector order resolves equal physical times.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimedAction {
    pub action: Action,
    pub time: i64,
}

/// Validate the explicit direct-mailbox contract. This never takes an untimed fast path.
pub fn assert_mailbox_supported_models(g: &ExecutionGraph) {
    for e in g.iter_events() {
        match g.label(e) {
            Label::Send {
                model: Model::Cd, ..
            } => {
                panic!("direct mailbox timing does not support Cd (send {e})");
            }
            Label::Recv {
                blocking: false,
                timing: ReceiveTiming::Abstract,
                ..
            } => {
                panic!("direct mailbox timing requires an explicit Timeout or Poll window for nonblocking receive {e}");
            }
            Label::Recv {
                blocking: true,
                timing,
                ..
            } if *timing != ReceiveTiming::Abstract => {
                panic!("blocking receive {e} must use Abstract timing; timed Timeout/Poll receives are nonblocking graph choices");
            }
            _ => {}
        }
    }
}

/// Full direct-mailbox verification, including original MUST consistency.
pub fn check_mailbox(g: &ExecutionGraph) -> TimedVerdict {
    assert_mailbox_supported_models(g);
    if !consistent(g) {
        return TimedVerdict::Infeasible(Explanation {
            atoms: vec![ExplainAtom::UntimedInconsistent],
        });
    }
    let builder = Builder::explaining(g);
    match solve(&builder.system) {
        Verdict::Sat { assignment } => TimedVerdict::Feasible(builder.schedule(&assignment)),
        Verdict::Unsat { cycle, .. } => TimedVerdict::Infeasible(builder.explanation(&cycle)),
    }
}

/// Feasibility only — the same verdict as `check_mailbox(g).is_feasible()`, without the
/// witness. This is the hot path of the terminal filter (one call per terminal candidate).
///
/// The constraint system is built with the explanation tables switched off
/// ([`Builder::explain`]); they never contribute an edge, so the `System` — and therefore
/// the solver verdict — is identical. A satisfiable system is re-verified through the full
/// [`check_mailbox`], so the witness-extraction assertions in [`Builder::schedule`] still
/// run on every accepted terminal; only the (overwhelmingly common) infeasible answer takes
/// the cheap path.
pub fn eager_mailbox_feasible(g: &ExecutionGraph) -> bool {
    assert_mailbox_supported_models(g);
    if !consistent(g) {
        return false;
    }
    if !solve(&Builder::build(g, false).system).is_sat() {
        return false;
    }
    // Sat: pay for the full builder once, so the witness is still extracted and checked.
    check_mailbox(g).is_feasible()
}

/// Sound pointwise lower bounds of the hard relaxation, gated by full feasibility.
/// `arr` and `avail` both denote actual mailbox delivery; every receive has a fire bound.
pub fn earliest_mailbox_times(g: &ExecutionGraph) -> Option<Earliest> {
    assert_mailbox_supported_models(g);
    if !consistent(g) {
        return None;
    }
    let builder = Builder::explaining(g);
    if !solve(&builder.system).is_sat() {
        return None;
    }
    let mut lower = vec![0i128; builder.system.n_vars as usize];
    for _ in 0..lower.len() {
        let mut changed = false;
        for e in &builder.system.hard {
            if e.y != ORIGIN {
                let candidate = lower[e.x as usize] - i128::from(e.w);
                if candidate > lower[e.y as usize] {
                    lower[e.y as usize] = candidate;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let bound =
        |v: VarId| i64::try_from(lower[v as usize]).expect("mailbox time lower bound exceeds i64");
    let mut result = Earliest::default();
    builder.each_var(&builder.arr, |s, v| {
        result.arr.insert(s, bound(v));
        result.avail.insert(s, bound(v));
    });
    builder.each_var(&builder.fire, |r, v| {
        result.fire.insert(r, bound(v));
    });
    Some(result)
}

/// Recheck the supplied times AND action order against the full formula, without solving.
/// Missing/duplicate actions, extra map entries, invalid ties and altered times fail.
pub fn verify_mailbox_schedule(g: &ExecutionGraph, schedule: &Schedule) -> bool {
    assert_mailbox_supported_models(g);
    if !consistent(g) {
        return false;
    }
    let b = Builder::explaining(g);
    if schedule.arr.len() != Builder::count_vars(&b.arr)
        || schedule.fire.len() != Builder::count_vars(&b.fire)
        || schedule.actions.len() != b.actions_len()
    {
        return false;
    }
    let mut assignment = vec![0i64; b.system.n_vars as usize];
    let mut missing = false;
    b.each_var(&b.arr, |s, v| match schedule.arr.get(&s) {
        Some(&time) => assignment[v as usize] = time,
        None => missing = true,
    });
    b.each_var(&b.fire, |r, v| match schedule.fire.get(&r) {
        Some(&time) => assignment[v as usize] = time,
        None => missing = true,
    });
    if missing {
        return false;
    }
    let mut positions = BTreeMap::new();
    let mut previous_time = 0;
    for (position, stamp) in schedule.actions.iter().enumerate() {
        // A forged schedule may name an action of an event outside `g`, so this lookup is
        // the checked one (the old `BTreeMap::get` simply missed).
        let Some((time, rank)) = b.action_vars_checked(stamp.action) else {
            return false;
        };
        if stamp.time < previous_time
            || stamp.time != assignment[time as usize]
            || positions.insert(stamp.action, position).is_some()
        {
            return false;
        }
        previous_time = stamp.time;
        if let Some(rank) = rank {
            let Ok(position) = i64::try_from(position) else {
                return false;
            };
            assignment[rank as usize] = position;
        }
    }
    let ordered =
        |edges: &[(Action, Action)]| edges.iter().all(|(a, b)| positions[a] < positions[b]);
    b.system.hard.iter().all(|&e| holds(e, &assignment))
        && ordered(&b.hard_order)
        && b.system
            .clauses
            .iter()
            .zip(&b.clause_order)
            .all(|(clause, orders)| {
                clause.alts.iter().zip(orders).any(|(edges, order)| {
                    edges.iter().all(|&e| holds(e, &assignment)) && ordered(order)
                })
            })
}

fn holds(e: Edge, assignment: &[i64]) -> bool {
    i128::from(assignment[e.x as usize]) - i128::from(assignment[e.y as usize]) <= i128::from(e.w)
}

#[derive(Default)]
struct Alternative {
    edges: Vec<Edge>,
    order: Vec<(Action, Action)>,
}

thread_local! {
    /// Per-thread pool of [`Builder`]s. Building one system per terminal candidate used to
    /// cost ~130 allocations (the edge vector and every clause alternative); recycling the
    /// whole builder makes the steady state allocation-free.
    static BUILDER_POOL: std::cell::RefCell<Vec<Builder>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// A [`Builder`] borrowed from [`BUILDER_POOL`] and returned on drop.
struct PooledBuilder(Option<Builder>);

impl PooledBuilder {
    fn take() -> Self {
        PooledBuilder(Some(
            BUILDER_POOL
                .with(|p| p.borrow_mut().pop())
                .unwrap_or_default(),
        ))
    }
}

impl std::ops::Deref for PooledBuilder {
    type Target = Builder;
    fn deref(&self) -> &Builder {
        self.0.as_ref().expect("builder lives until drop")
    }
}

impl std::ops::DerefMut for PooledBuilder {
    fn deref_mut(&mut self) -> &mut Builder {
        self.0.as_mut().expect("builder lives until drop")
    }
}

impl Drop for PooledBuilder {
    fn drop(&mut self) {
        if let Some(b) = self.0.take() {
            BUILDER_POOL.with(|p| p.borrow_mut().push(b));
        }
    }
}

/// The graph's events flattened to a dense `0..n` index, so every per-event table of
/// [`Builder`] is an array lookup instead of a `BTreeMap` probe. `events` is in `(tid, idx)`
/// order, which is `EventId`'s `Ord`, so "iterate the dense table" and "iterate the old
/// `BTreeMap`" are the same sequence.
#[derive(Default)]
struct EventIndex {
    /// First dense index of each thread (`len = num_threads`).
    base: Vec<u32>,
    /// Dense index → `EventId`.
    events: Vec<EventId>,
}

impl EventIndex {
    fn rebuild(&mut self, g: &ExecutionGraph) {
        self.base.clear();
        self.events.clear();
        for tid in 0..g.num_threads() {
            self.base.push(self.events.len() as u32);
            for idx in 0..g.thread_len(tid) {
                self.events.push(EventId::new(tid, idx));
            }
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.events.len()
    }

    /// Dense index of `e`, which must be an event of the indexed graph.
    #[inline]
    fn of(&self, e: EventId) -> usize {
        self.base[e.tid] as usize + e.idx
    }
}

#[derive(Default)]
struct Builder {
    system: System,
    index: EventIndex,
    /// Per-event arrival / fire / clock variables, `NO_VAR` where the event has none.
    arr: Vec<VarId>,
    fire: Vec<VarId>,
    start: Vec<VarId>,
    /// `(time, rank)` variable of each action, indexed `kind * n_events + dense(event)`;
    /// `NO_VAR` for "this action does not exist" / "unranked".
    actions: Vec<(VarId, VarId)>,
    hard_order: Vec<(Action, Action)>,
    clause_order: Vec<Vec<Vec<(Action, Action)>>>,
    provenance: BTreeMap<(VarId, VarId, i64), ExplainAtom>,
    ranked: bool,
    /// `consumer[dense(s)]` = the receive that reads `s` (at most one in a well-formed
    /// graph); the dense twin of the old `BTreeMap<send, recv>`.
    consumer: Vec<Option<EventId>>,
    /// Scratch for the per-receive "still unconsumed matching sources" list.
    remaining: Vec<EventId>,
    /// Recycled vector storage. A `Builder` is taken from a per-thread pool and reset, so
    /// the steady state (one system per terminal candidate, millions of them) performs no
    /// allocation at all: these hold the `Vec`s that the previous system's clauses used.
    spare_edges: Vec<Vec<Edge>>,
    spare_orders: Vec<Vec<(Action, Action)>>,
    spare_alt_lists: Vec<Vec<Vec<Edge>>>,
    spare_alts: Vec<Vec<Alternative>>,
    /// Whether to record the witness/explanation side tables (`provenance`, `hard_order`,
    /// `clause_order`). They feed [`Builder::explanation`], [`Builder::schedule`] and
    /// [`verify_mailbox_schedule`] only — never [`Builder::system`] — so building them is
    /// pure overhead when the caller wants nothing but a feasibility bit. Skipping them
    /// leaves the emitted `System` bit-for-bit identical (the same edges pushed in the same
    /// order), hence the solver verdict is identical; `debug_assert`s in
    /// [`eager_mailbox_feasible`] and `tests/mailbox_oracle_corpus.rs` pin that.
    explain: bool,
}

impl Builder {
    /// The full builder, with witness/explanation tables. Use
    /// [`build`](Self::build)`(g, false)` when only `system` is needed.
    fn explaining(g: &ExecutionGraph) -> PooledBuilder {
        Self::build(g, true)
    }

    /// A reset builder from the per-thread pool, fully populated for `g`.
    fn build(g: &ExecutionGraph, explain: bool) -> PooledBuilder {
        let mut b = PooledBuilder::take();
        b.populate(g, explain);
        b
    }

    /// Return every buffer to its empty state, recycling the previous system's clause
    /// vectors, and rebuild the tables for `g`.
    fn populate(&mut self, g: &ExecutionGraph, explain: bool) {
        // Recycle the clause storage of the previous system before clearing it.
        for clause in self.system.clauses.drain(..) {
            let mut alts = clause.alts;
            for mut edges in alts.drain(..) {
                edges.clear();
                self.spare_edges.push(edges);
            }
            self.spare_alt_lists.push(alts);
        }
        for orders in self.clause_order.drain(..) {
            for mut o in orders {
                o.clear();
                self.spare_orders.push(o);
            }
        }
        self.system.hard.clear();
        self.system.n_vars = 1;
        self.hard_order.clear();
        self.provenance.clear();
        self.explain = explain;
        self.ranked = g.iter_sends().any(|s| g.send_model(s) != Some(Model::Asyn));
        self.index.rebuild(g);
        let n = self.index.len();
        self.arr.clear();
        self.arr.resize(n, NO_VAR);
        self.fire.clear();
        self.fire.resize(n, NO_VAR);
        self.start.clear();
        self.start.resize(n, NO_VAR);
        self.actions.clear();
        self.actions.resize(KINDS * n, (NO_VAR, NO_VAR));
        self.consumer.clear();
        self.consumer.resize(n, None);
        let b = self;
        for i in 0..n {
            let e = b.index.events[i];
            if g.label(e).is_send() {
                b.arr[i] = b.variable();
            }
            if g.label(e).is_recv() {
                b.fire[i] = b.variable();
            }
        }
        for tid in 0..g.num_threads() {
            let mut clock = ORIGIN;
            let mut previous = None;
            for idx in 0..g.thread_len(tid) {
                let e = EventId::new(tid, idx);
                let i = b.index.of(e);
                b.start[i] = clock;
                let (first, last) = match g.label(e) {
                    Label::Send { window, .. } => {
                        let arr = b.arr[i];
                        b.action(Action::Send(e), clock);
                        b.action(Action::Deliver(e), arr);
                        b.order(Action::Send(e), Action::Deliver(e));
                        b.window(
                            clock,
                            arr,
                            *window,
                            ExplainAtom::WindowLo(e),
                            ExplainAtom::WindowHi(e),
                        );
                        (Action::Send(e), Action::Send(e))
                    }
                    Label::Recv { .. } => {
                        let fire = b.fire[i];
                        b.action(Action::Invoke(e), clock);
                        b.action(Action::Complete(e), fire);
                        b.order(Action::Invoke(e), Action::Complete(e));
                        clock = fire;
                        (Action::Invoke(e), Action::Complete(e))
                    }
                    _ => {
                        b.action(Action::Local(e), clock);
                        (Action::Local(e), Action::Local(e))
                    }
                };
                if let Some(previous) = previous {
                    b.order(previous, first);
                }
                previous = Some(last);
            }
        }
        b.transport(g);
        for r in g.iter_recvs() {
            if let Some(s) = g.reads_from(r) {
                if g.contains(s) {
                    let i = b.index.of(s);
                    b.consumer[i] = Some(r);
                }
            }
        }
        for r in g.iter_recvs() {
            let mut remaining = std::mem::take(&mut b.remaining);
            remaining.clear();
            remaining.extend(g.iter_sends().filter(|&s| {
                g.matches(s, r)
                    && !b.consumer[b.index.of(s)].is_some_and(|q| q.tid == r.tid && q.idx < r.idx)
            }));
            b.receive(g, r, &remaining);
            b.remaining = remaining;
        }
    }

    /// `(time, rank)` of an action, as the old `actions[&a]` returned it.
    #[inline]
    fn action_vars(&self, a: Action) -> (VarId, Option<VarId>) {
        let (time, rank) = self.actions[a.kind() * self.index.len() + self.index.of(a.event())];
        debug_assert_ne!(
            time, NO_VAR,
            "order refers to an action that was never created"
        );
        (time, (rank != NO_VAR).then_some(rank))
    }

    /// [`action_vars`](Self::action_vars) for an action that may not belong to this graph at
    /// all — the `BTreeMap::get` of the dense tables.
    fn action_vars_checked(&self, a: Action) -> Option<(VarId, Option<VarId>)> {
        let e = a.event();
        if e.tid >= self.index.base.len() {
            return None;
        }
        let i = self.index.base[e.tid] as usize + e.idx;
        // The thread's events are contiguous, so staying inside this thread's block is the
        // whole bound check.
        let end = self
            .index
            .base
            .get(e.tid + 1)
            .map_or(self.index.len(), |&b| b as usize);
        if i >= end {
            return None;
        }
        let (time, rank) = self.actions[a.kind() * self.index.len() + i];
        (time != NO_VAR).then_some((time, (rank != NO_VAR).then_some(rank)))
    }

    /// Every created action with its variables, in `Action`'s `Ord` order — the sequence a
    /// `BTreeMap<Action, _>` used to yield.
    fn each_action(&self, mut f: impl FnMut(Action, VarId, Option<VarId>)) {
        let n = self.index.len();
        for kind in 0..KINDS {
            for (i, &e) in self.index.events.iter().enumerate() {
                let (time, rank) = self.actions[kind * n + i];
                if time != NO_VAR {
                    f(
                        Action::of_kind(kind, e),
                        time,
                        (rank != NO_VAR).then_some(rank),
                    );
                }
            }
        }
    }

    fn actions_len(&self) -> usize {
        self.actions.iter().filter(|&&(t, _)| t != NO_VAR).count()
    }

    /// Per-event variables of `table` (`arr` / `fire`) in `EventId` order.
    fn each_var(&self, table: &[VarId], mut f: impl FnMut(EventId, VarId)) {
        for (i, &v) in table.iter().enumerate() {
            if v != NO_VAR {
                f(self.index.events[i], v);
            }
        }
    }

    fn count_vars(table: &[VarId]) -> usize {
        table.iter().filter(|&&v| v != NO_VAR).count()
    }

    fn variable(&mut self) -> VarId {
        let v = self.system.n_vars;
        self.system.n_vars = v
            .checked_add(1)
            .expect("mailbox solver variable count exceeds u32");
        self.system.hard.push(Edge {
            x: ORIGIN,
            y: v,
            w: 0,
        });
        v
    }

    fn action(&mut self, a: Action, time: VarId) {
        let rank = if self.ranked { self.variable() } else { NO_VAR };
        let slot = a.kind() * self.index.len() + self.index.of(a.event());
        self.actions[slot] = (time, rank);
    }

    fn edge(&mut self, edge: Edge, atom: ExplainAtom) {
        if self.explain {
            self.provenance.insert((edge.x, edge.y, edge.w), atom);
        }
        self.system.hard.push(edge);
    }

    fn window(&mut self, start: VarId, end: VarId, w: Window, lo: ExplainAtom, hi: ExplainAtom) {
        self.edge(
            Edge {
                x: start,
                y: end,
                w: -(w.lo() as i64),
            },
            lo,
        );
        if let Some(upper) = w.hi() {
            self.edge(
                Edge {
                    x: end,
                    y: start,
                    w: upper as i64,
                },
                hi,
            );
        }
    }

    /// The (one or two) edges expressing `a` before `b`, written into `out` rather than a
    /// fresh `Vec`: this runs once per `order`/clause alternative and the allocation was
    /// showing up as a cost of its own.
    fn order_edges_into(&self, a: Action, b: Action, out: &mut Vec<Edge>) {
        let (at, ar) = self.action_vars(a);
        let (bt, br) = self.action_vars(b);
        out.push(Edge { x: at, y: bt, w: 0 });
        if let (Some(ar), Some(br)) = (ar, br) {
            out.push(Edge {
                x: ar,
                y: br,
                w: -1,
            });
        }
    }

    fn order(&mut self, before: Action, after: Action) {
        let (at, ar) = self.action_vars(before);
        let (bt, br) = self.action_vars(after);
        let mut edges = [Edge { x: at, y: bt, w: 0 }; 2];
        let mut count = 1;
        if let (Some(ar), Some(br)) = (ar, br) {
            edges[1] = Edge {
                x: ar,
                y: br,
                w: -1,
            };
            count = 2;
        }
        for &edge in &edges[..count] {
            self.edge(edge, ExplainAtom::MailboxOrder { before, after });
        }
        if self.explain {
            self.hard_order.push((before, after));
        }
    }

    /// An empty [`Alternative`] built from recycled vectors.
    fn alternative(&mut self) -> Alternative {
        Alternative {
            edges: self.spare_edges.pop().unwrap_or_default(),
            order: self.spare_orders.pop().unwrap_or_default(),
        }
    }

    fn clause(&mut self, mut alternatives: Vec<Alternative>, atom: ExplainAtom) {
        let mut alts = self.spare_alt_lists.pop().unwrap_or_default();
        let mut orders = Vec::new();
        for alt in alternatives.drain(..) {
            let mut edges = alt.edges;
            for &(a, b) in &alt.order {
                self.order_edges_into(a, b, &mut edges);
            }
            if self.explain {
                for edge in &edges {
                    self.provenance.insert((edge.x, edge.y, edge.w), atom);
                }
                orders.push(alt.order);
            } else {
                let mut order = alt.order;
                order.clear();
                self.spare_orders.push(order);
            }
            alts.push(edges);
        }
        alternatives.clear();
        self.spare_alts.push(alternatives);
        self.system.clauses.push(Clause { alts });
        if self.explain {
            self.clause_order.push(orders);
        }
    }

    fn transport(&mut self, g: &ExecutionGraph) {
        let mut channels = BTreeMap::new();
        let mut mailbox = Vec::new();
        for s in g.iter_sends() {
            match g.label(s) {
                Label::Send {
                    model: Model::P2p,
                    dst,
                    ..
                } => {
                    if let Some(prev) = channels.insert((s.tid, *dst), s) {
                        self.order(Action::Deliver(prev), Action::Deliver(s));
                    }
                }
                Label::Send {
                    model: Model::Mbox, ..
                } => mailbox.push(s),
                _ => {}
            }
        }
        for (i, &a) in mailbox.iter().enumerate() {
            for &b in &mailbox[i + 1..] {
                if g.label(a).dst() != g.label(b).dst() {
                    continue;
                }
                let before = |this: &mut Self, a: EventId, b: EventId| {
                    let mut alt = this.alternative();
                    alt.order.push((Action::Send(a), Action::Send(b)));
                    alt.order.push((Action::Deliver(a), Action::Deliver(b)));
                    alt
                };
                // Existing causality fixes the send order; avoid a redundant disjunction.
                if g.porf_reaches(a, b) {
                    self.order(Action::Send(a), Action::Send(b));
                    self.order(Action::Deliver(a), Action::Deliver(b));
                } else if g.porf_reaches(b, a) {
                    self.order(Action::Send(b), Action::Send(a));
                    self.order(Action::Deliver(b), Action::Deliver(a));
                } else {
                    let first = before(self, a, b);
                    let second = before(self, b, a);
                    let mut list = self.spare_alts.pop().unwrap_or_default();
                    list.push(first);
                    list.push(second);
                    self.clause(
                        list,
                        ExplainAtom::MailboxOrder {
                            before: Action::Deliver(a),
                            after: Action::Deliver(b),
                        },
                    );
                }
            }
        }
    }

    fn receive(&mut self, g: &ExecutionGraph, r: EventId, remaining: &[EventId]) {
        let ri = self.index.of(r);
        let a = self.start[ri];
        let f = self.fire[ri];
        let timing = g.label(r).receive_timing().unwrap();
        let source = g.reads_from(r);
        let window = match timing {
            ReceiveTiming::Abstract => None,
            ReceiveTiming::Timeout(w) | ReceiveTiming::Poll(w) => Some(w),
        };
        if source.is_none() || matches!(timing, ReceiveTiming::Poll(_)) {
            self.window(
                a,
                f,
                window.expect("an empty result requires timed receive metadata"),
                ExplainAtom::ReceiveWindow(r),
                ExplainAtom::ReceiveWindow(r),
            );
        }
        let Some(s) = source else {
            for &m in remaining {
                self.order(Action::Complete(r), Action::Deliver(m));
            }
            return;
        };
        self.order(Action::Deliver(s), Action::Complete(r));
        // Original Mbox selective receive cannot skip a remaining matching Mbox source
        // even when several messages were queued before invocation.
        if g.send_model(s) == Some(Model::Mbox) {
            for &m in remaining {
                if m != s && g.send_model(m) == Some(Model::Mbox) {
                    self.order(Action::Send(s), Action::Send(m));
                    self.order(Action::Deliver(s), Action::Deliver(m));
                }
            }
        }
        if matches!(timing, ReceiveTiming::Poll(_)) {
            return;
        }
        if let ReceiveTiming::Timeout(w) = timing {
            if let Some(hi) = w.hi() {
                self.edge(
                    Edge {
                        x: f,
                        y: a,
                        w: hi as i64,
                    },
                    ExplainAtom::ReceiveWindow(r),
                );
            }
        }
        let arr_s = self.arr[self.index.of(s)];
        let mut queued = self.alternative();
        queued.edges.push(Edge { x: f, y: a, w: 0 });
        queued.edges.push(Edge { x: a, y: f, w: 0 });
        queued.order.push((Action::Deliver(s), Action::Invoke(r)));
        let mut waiting = self.alternative();
        waiting.edges.push(Edge {
            x: f,
            y: arr_s,
            w: 0,
        });
        waiting.edges.push(Edge {
            x: arr_s,
            y: f,
            w: 0,
        });
        waiting.order.push((Action::Invoke(r), Action::Deliver(s)));
        waiting.order.extend(
            remaining
                .iter()
                .filter(|&&m| m != s)
                .map(|&m| (Action::Deliver(s), Action::Deliver(m))),
        );
        let mut list = self.spare_alts.pop().unwrap_or_default();
        list.push(queued);
        list.push(waiting);
        self.clause(list, ExplainAtom::BranchB(r));
    }

    fn schedule(&self, assignment: &[i64]) -> Schedule {
        let mut schedule = Schedule::default();
        self.each_var(&self.arr, |s, v| {
            schedule.arr.insert(s, assignment[v as usize]);
        });
        self.each_var(&self.fire, |r, v| {
            schedule.fire.insert(r, assignment[v as usize]);
        });
        // Reconstruct an action DAG even for the rank-free Asyn solver. Its acyclicity
        // follows from the Asyn theorem; this also independently checks witness extraction.
        let mut order = self.hard_order.clone();
        for (clause, alternatives) in self.system.clauses.iter().zip(&self.clause_order) {
            let index = clause
                .alts
                .iter()
                .position(|edges| edges.iter().all(|&e| holds(e, assignment)))
                .expect("solver assignment violates mailbox receive/delivery clause");
            order.extend(&alternatives[index]);
        }
        let mut incoming: BTreeMap<Action, usize> = BTreeMap::new();
        self.each_action(|a, _, _| {
            incoming.insert(a, 0);
        });
        let mut outgoing: BTreeMap<Action, Vec<Action>> = BTreeMap::new();
        for (a, b) in order {
            *incoming.get_mut(&b).unwrap() += 1;
            outgoing.entry(a).or_default().push(b);
        }
        let mut ready = BTreeSet::new();
        for (&a, &count) in &incoming {
            if count == 0 {
                ready.insert((assignment[self.action_vars(a).0 as usize], a));
            }
        }
        while let Some((time, action)) = ready.pop_first() {
            schedule.actions.push(TimedAction { action, time });
            for &next in outgoing.get(&action).into_iter().flatten() {
                let count = incoming.get_mut(&next).unwrap();
                *count -= 1;
                if *count == 0 {
                    ready.insert((assignment[self.action_vars(next).0 as usize], next));
                }
            }
        }
        assert_eq!(
            schedule.actions.len(),
            self.actions_len(),
            "mailbox witness action cycle"
        );
        assert!(
            schedule.actions.windows(2).all(|p| p[0].time <= p[1].time),
            "mailbox witness goes backwards in physical time"
        );
        schedule
    }

    fn explanation(&self, cycle: &[Edge]) -> Explanation {
        let mut atoms = Vec::new();
        for e in cycle {
            if let Some(&atom) = self.provenance.get(&(e.x, e.y, e.w)) {
                if !atoms.contains(&atom) {
                    atoms.push(atom);
                }
            }
        }
        Explanation { atoms }
    }
}
