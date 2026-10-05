//! G1-accept oracles for the full eager-time predicate search (`Config::with_time_predicate`,
//! the T2 extension — see `T2_PLAN.md`). These pin the four coupled pieces (T-DES / T-CANON /
//! T-PRED / T-GATE) with:
//!
//!   * unit tests for the DES scheduling order and the time-aware canonical tiebreaker;
//!   * an equivalence check `realizable(T2) == realizable(T1-filter)` on hand-built programs,
//!     with no duplicate keys and (on the exact-`possible_future` `SeqProgram`) zero dead
//!     branches;
//!   * the 6-thread L3 regression, where the refuted-L3 forced-closure gate must keep the search
//!     out of the fruitless `r←s` subtree (full = 2, 0 dead branches), which a T1-style
//!     terminal-count check cannot see.
//!
//! The differential fuzz (the strongest check) lives in `fuzz_timed.rs`.

mod common;

use std::collections::BTreeSet;

use common::SeqProgram;
use must::event::{Label, Model, Pred, Window};
use must::explorer::revisit::get_cons_tiebreaker;
use must::graph::ExecutionGraph;
use must::scheduler::{pick, NextStep};
use must::{
    explore, traces_of, Config, CountingObserver, DeadBranchDetector, ExecutionCollector, Program,
};

/// A finite-window send.
fn tsend(model: Model, dst: usize, v: &str, lo: u64, hi: u64) -> Label {
    Label::send_within(model, dst, v, Window::new(lo, hi))
}

// -- T-DES: discrete-event scheduling order (scheduler::pick under the predicate) ----------

/// Which thread the DES policy picks next at graph `g` of program `prog`.
fn des_pick(prog: &SeqProgram, g: &ExecutionGraph) -> NextStep {
    let traces = traces_of(g, prog.num_threads());
    let nexts = prog.next(&traces);
    pick(
        g,
        &nexts,
        &(0..prog.num_threads()).collect::<Vec<_>>(),
        true,
    )
}

/// Sends bubble up by lower-bound arrival time (`Occ + window.lo`), regardless of tid order.
#[test]
fn des_orders_sends_by_lb() {
    // T0's send arrives at [10,20]; T1's at [1,2]; T2 receives. Despite T0 < T1 by tid, the
    // earlier-arriving T1 send is drained first.
    let prog = SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 2, "a", 10, 20)],
        vec![tsend(Model::Asyn, 2, "b", 1, 2)],
        vec![Label::recv(Pred::any())],
    ]);

    let g0 = ExecutionGraph::new();
    match des_pick(&prog, &g0) {
        NextStep::Event { tid, .. } => assert_eq!(tid, 1, "the earlier-arriving send (T1, LB=1)"),
        NextStep::Terminal { .. } => panic!("expected an event"),
    }

    // After draining T1's send, T0's send (LB=10) is next; the receive stays parked (drain-first).
    let mut g1 = ExecutionGraph::new();
    g1.add_event(1, tsend(Model::Asyn, 2, "b", 1, 2));
    match des_pick(&prog, &g1) {
        NextStep::Event { tid, .. } => assert_eq!(tid, 0, "the later send (T0, LB=10) drains next"),
        NextStep::Terminal { .. } => panic!("expected an event"),
    }

    // With both sends present, only the blocking receive remains: phase B wakes it.
    let mut g2 = g1.clone();
    g2.add_event(0, tsend(Model::Asyn, 2, "a", 10, 20));
    match des_pick(&prog, &g2) {
        NextStep::Event { tid, .. } => assert_eq!(tid, 2, "phase B wakes the receiver"),
        NextStep::Terminal { .. } => panic!("expected an event"),
    }
}

/// Phase B wakes the blocking receive with the minimum `fire_lb` (earliest guaranteed message).
#[test]
fn des_wakes_earliest_firing_receive() {
    // Two receivers: T2 can read a fast [1,1] message, T3 only a slow [50,50] one. Both are
    // wakeable at the graph with both sends present; the fast one fires first.
    let prog = SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 2, "f", 1, 1)],
        vec![tsend(Model::Asyn, 3, "s", 50, 50)],
        vec![Label::recv(Pred::any())],
        vec![Label::recv(Pred::any())],
    ]);
    let mut g = ExecutionGraph::new();
    g.add_event(0, tsend(Model::Asyn, 2, "f", 1, 1));
    g.add_event(1, tsend(Model::Asyn, 3, "s", 50, 50));
    match des_pick(&prog, &g) {
        NextStep::Event { tid, .. } => assert_eq!(tid, 2, "T2 fires at 1 before T3 at 50"),
        NextStep::Terminal { .. } => panic!("expected an event"),
    }
}

// -- T-CANON: time-aware canonical tiebreaker (get_cons_tiebreaker under the predicate) -----

/// Under the predicate the canonical source is the earliest-arriving (`avail`-LB) one, not the
/// `(tid, idx)`-minimal; both must be *feasible* to read. Here r1 fires late (occ = 100 from the
/// selective r0←t), so both x[20] and y[10] are readable via the A-clause — the tiebreaker picks
/// the earlier-arriving y despite its larger tid.
#[test]
fn canon_prefers_earliest_avail_under_predicate() {
    let mut h = ExecutionGraph::new();
    let t = h.add_event(0, tsend(Model::Asyn, 2, "t", 100, 100));
    let x = h.add_event(1, tsend(Model::Asyn, 2, "x", 20, 20)); // tid 1, avail 20
    let r0 = h.add_event(2, Label::recv(Pred::eq("t")));
    let r1 = h.add_event(2, Label::recv(Pred::any()));
    let y = h.add_event(3, tsend(Model::Asyn, 2, "y", 10, 10)); // tid 3, avail 10
    h.set_rf(r0, Some(t));

    // Untimed: (tid, idx)-minimal is x (tid 1).
    assert_eq!(get_cons_tiebreaker(&h, r1, false), Some(x));
    // Time-aware: the earliest-arriving is y (avail 10 < 20), despite tid 3 > 1.
    assert_eq!(get_cons_tiebreaker(&h, r1, true), Some(y));
}

/// When only the earliest source is feasible (mutual competitors, no A-clause escape), the
/// predicate tiebreaker returns exactly that one; the untimed one still returns the (tid,idx)-min.
#[test]
fn canon_filters_infeasible_source() {
    // r fires at occ 0; reading the late m[30,30] is infeasible (its competitor n[5,5] can never
    // be as-late), so only n survives the feasibility filter.
    let mut h = ExecutionGraph::new();
    let m = h.add_event(0, tsend(Model::Asyn, 2, "m", 30, 30)); // tid 0
    let n = h.add_event(1, tsend(Model::Asyn, 2, "n", 5, 5)); // tid 1
    let r = h.add_event(2, Label::recv(Pred::any()));
    let _ = (m, r);

    // Untimed: (tid, idx)-minimal is m (tid 0).
    assert_eq!(get_cons_tiebreaker(&h, r, false), Some(m));
    // Time-aware: reading m is infeasible, so the canonical source is n.
    assert_eq!(get_cons_tiebreaker(&h, r, true), Some(n));
}

// -- Equivalence: realizable(T2) == realizable(T1-filter) -----------------------------------

/// The realizable full+blocked canonical keys under the T2 predicate.
fn t2_realizable_keys(prog: &SeqProgram) -> BTreeSet<String> {
    let col = ExecutionCollector::new();
    let dead = DeadBranchDetector::new();
    let obs = (col, dead);
    explore(
        || prog.clone(),
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let (col, dead) = obs;
    // On a SeqProgram (exact possible_future) the forced-closure gate is exact ⇒ no dead branch.
    assert_eq!(
        dead.dead(),
        0,
        "T2 must have no dead Visit nodes on a SeqProgram (of {} visits)",
        dead.visits()
    );
    let keys = col.terminal_keys();
    let set: BTreeSet<String> = keys.iter().cloned().collect();
    assert_eq!(keys.len(), set.len(), "T2 produced duplicate terminal keys");
    set
}

/// The realizable full+blocked canonical keys under the T1 filter (the reference).
fn t1_realizable_keys(prog: &SeqProgram) -> BTreeSet<String> {
    let col = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &col,
        Config::default().collect_errors().with_time_filter(),
    );
    col.terminal_keys().into_iter().collect()
}

/// Assert T2 reproduces the T1-filter realizable terminal set exactly.
fn assert_t2_matches_t1(name: &str, prog: &SeqProgram) {
    let t2 = t2_realizable_keys(prog);
    let t1 = t1_realizable_keys(prog);
    assert_eq!(
        t2, t1,
        "{name}: T2 realizable keys != T1-filter realizable keys"
    );
}

#[test]
fn t2_matches_t1_two_senders_gap() {
    // Two senders, one late [30,40], one early [0,1]; the receiver reads whichever. Reading the
    // late one is filtered by T1 / never realized by T2 (competitor escapes only via A-clause).
    assert_t2_matches_t1(
        "two_senders_gap",
        &SeqProgram::new(vec![
            vec![tsend(Model::Asyn, 2, "a", 30, 40)],
            vec![tsend(Model::Asyn, 2, "b", 0, 1)],
            vec![Label::recv(Pred::any())],
        ]),
    );
}

#[test]
fn t2_matches_t1_two_receives() {
    // Two receives consume two sends; both orderings are realizable (the reply chain, occ moves).
    assert_t2_matches_t1(
        "two_receives",
        &SeqProgram::new(vec![
            vec![tsend(Model::Asyn, 2, "a", 1, 3)],
            vec![tsend(Model::Asyn, 2, "b", 2, 4)],
            vec![Label::recv(Pred::any()), Label::recv(Pred::any())],
        ]),
    );
}

#[test]
fn t2_matches_t1_p2p_gating() {
    // P2p FIFO: T0 sends m1[50,50] then m2[1,1] to T2; reading m2 first gates fire at 50.
    assert_t2_matches_t1(
        "p2p_gating",
        &SeqProgram::new(vec![
            vec![
                tsend(Model::P2p, 2, "m1", 50, 50),
                tsend(Model::P2p, 2, "m2", 1, 1),
            ],
            vec![],
            vec![Label::recv(Pred::any()), Label::recv(Pred::any())],
        ]),
    );
}

#[test]
fn t2_matches_t1_selective_receive() {
    // A selective receive collapses the choice; the reply thread adds a second round.
    assert_t2_matches_t1(
        "selective",
        &SeqProgram::new(vec![
            vec![tsend(Model::Asyn, 2, "x", 0, 5)],
            vec![tsend(Model::Asyn, 2, "y", 0, 5)],
            vec![Label::recv(Pred::eq("y")), Label::recv(Pred::eq("x"))],
        ]),
    );
}

#[test]
fn t2_matches_t1_nonblocking_recv() {
    // A non-blocking receive (time-transparent in v1) reads ⊥ or the send; both realizable.
    assert_t2_matches_t1(
        "nonblocking",
        &SeqProgram::new(vec![
            vec![tsend(Model::Asyn, 1, "a", 3, 5)],
            vec![Label::recv_nb(Pred::any())],
        ]),
    );
}

// -- L3 regression at the explorer level (T2_PLAN §5в) --------------------------------------

/// The 6-thread L3 counterexample program (TIME_PLAN "Контрпример").
fn l3_program() -> SeqProgram {
    SeqProgram::new(vec![
        vec![Label::recv(Pred::any())],           // T0: r
        vec![tsend(Model::Asyn, 0, "a", 1, 100)], // T1: a
        vec![
            Label::recv(Pred::eq("g")),
            tsend(Model::Asyn, 0, "b0", 0, 0),
        ], // T2: rg; m
        vec![tsend(Model::Asyn, 2, "g", 5, 5)],   // T3: g
        vec![Label::recv(Pred::eq("x")), tsend(Model::Asyn, 0, "b", 0, 0)], // T4: rs; s
        vec![tsend(Model::Asyn, 4, "x", 30, 30)], // T5: x
    ])
}

/// L3: under T2 the search yields exactly the two realizable terminals r←a and r←m, with **zero**
/// dead branches — the forced-closure gate rejects the s→r revisit before entering its fruitless
/// Visit(G′). T1-filter sees full=2 / filtered=1 (it does generate the infeasible r←s); the
/// dead-branch count is the extra invariant a terminal-count check cannot see (T2_PLAN §5в).
#[test]
fn l3_explorer_regression() {
    let prog = l3_program();

    // T1-filter reference: 2 realizable full, 1 filtered (r←s), 0 blocked.
    let (t1_counts, t1_col) = {
        let obs = (CountingObserver::new(), ExecutionCollector::new());
        explore(
            || prog.clone(),
            &obs,
            Config::default().collect_errors().with_time_filter(),
        );
        obs
    };
    assert_eq!(
        t1_counts.full(),
        2,
        "T1: two realizable full terminals (r←a, r←m)"
    );
    assert_eq!(
        t1_counts.filtered_full(),
        1,
        "T1: one filtered full terminal (r←s)"
    );
    assert_eq!(t1_counts.blocked(), 0);

    // T2 predicate: same 2 realizable full, 0 blocked, 0 filtered (predicate = no filter), and
    // crucially 0 dead branches (the gate prevents the fruitless r←s Visit).
    let obs = (
        (CountingObserver::new(), ExecutionCollector::new()),
        DeadBranchDetector::new(),
    );
    explore(
        || prog.clone(),
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let ((t2_counts, t2_col), dead) = obs;
    assert_eq!(t2_counts.full(), 2, "T2: two realizable full terminals");
    assert_eq!(t2_counts.blocked(), 0, "T2: no blocked terminals");
    assert_eq!(t2_counts.filtered(), 0, "T2: the predicate never filters");
    assert_eq!(
        dead.dead(),
        0,
        "T2: no dead branches — the forced-closure gate must reject s→r (of {} visits)",
        dead.visits()
    );

    // The realizable sets coincide (r←a and r←m), and exclude r←s.
    let t1_keys: BTreeSet<String> = t1_col.terminal_keys().into_iter().collect();
    let t2_keys: BTreeSet<String> = t2_col.terminal_keys().into_iter().collect();
    assert_eq!(
        t2_keys, t1_keys,
        "L3: T2 realizable set must equal T1-filter realizable set"
    );
}

/// The L3 counterexample built on the **coroutine runtime** (`System`) instead of a table
/// program — the H1 regression, in both halves.
///
/// `make(declare)` builds L3 as six coroutine bodies; with `declare` it also hands each thread a
/// `possible_future` tail ([`System::declare_future`]), which is *exact* here because no body
/// branches on a received value.
///
/// Why the two halves differ: catching L3 needs the closure to contain `rg←g` **and** the `m` it
/// unlocks, and [`must::time`]'s C1-sound rule only forces a blocking receive when the futures
/// prove its source unavoidable. Undeclared (`possible_future = None`) it declines, the closure
/// stops at `G′` itself, the gate sees a feasible graph and the fruitless `Visit(G′)` subtree
/// runs. Declared, the receive is forced, `m` is drained behind it, the closure comes out
/// infeasible and the s→r revisit is rejected outright.
///
/// Both halves must agree with the T1 filter key for key — the declaration buys *optimality*,
/// never a different answer.
fn l3_runtime(declare: bool) -> must::System {
    use must::event::Label;
    use must::{Ctx, System, Window};

    let win = |lo, hi| Window::new(lo, hi);
    let mut sys = System::new();
    // T0: r = recv(any)
    sys.add(|c: Ctx| async move {
        c.recv(|_: &str| true).await;
    });
    // T1: a = send(T0, "a", [1,100])
    sys.add(|c: Ctx| async move {
        c.send_within(0, "a", Model::Asyn, Window::new(1, 100));
    });
    // T2: rg = recv(= "g"); m = send(T0, "b0", [0,0])
    sys.add(|c: Ctx| async move {
        c.recv(|x: &str| x == "g").await;
        c.send_within(0, "b0", Model::Asyn, Window::new(0, 0));
    });
    // T3: g = send(T2, "g", [5,5])
    sys.add(|c: Ctx| async move {
        c.send_within(2, "g", Model::Asyn, Window::new(5, 5));
    });
    // T4: rs = recv(= "x"); s = send(T0, "b", [0,0])
    sys.add(|c: Ctx| async move {
        c.recv(|x: &str| x == "x").await;
        c.send_within(0, "b", Model::Asyn, Window::new(0, 0));
    });
    // T5: x = send(T4, "x", [30,30])
    sys.add(|c: Ctx| async move {
        c.send_within(4, "x", Model::Asyn, Window::new(30, 30));
    });

    if declare {
        // Labels *after* the thread's next event; the runtime supplies the next one itself.
        for tid in [0, 1, 3, 5] {
            sys.declare_future(tid, |_| Vec::new()); // single-event threads
        }
        let m = Label::send_within(Model::Asyn, 0, "b0", win(0, 0));
        sys.declare_future(2, move |trace: &[Option<must::Val>]| {
            if trace.is_empty() {
                vec![m.clone()]
            } else {
                Vec::new()
            }
        });
        let s = Label::send_within(Model::Asyn, 0, "b", win(0, 0));
        sys.declare_future(4, move |trace: &[Option<must::Val>]| {
            if trace.is_empty() {
                vec![s.clone()]
            } else {
                Vec::new()
            }
        });
    }
    sys
}

/// Run L3-on-the-runtime under the T2 predicate and return `(realizable keys, dead, visits)`.
fn l3_runtime_run(declare: bool) -> (BTreeSet<String>, usize, usize) {
    let obs = (
        (CountingObserver::new(), ExecutionCollector::new()),
        DeadBranchDetector::new(),
    );
    explore(
        || l3_runtime(declare),
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let ((counts, col), dead) = obs;
    assert_eq!(counts.full(), 2, "the two realizable terminals r←a, r←m");
    assert_eq!(counts.blocked(), 0);
    assert_eq!(counts.filtered(), 0, "the predicate never filters");
    (
        col.terminal_keys().into_iter().collect(),
        dead.dead(),
        dead.visits(),
    )
}

#[test]
fn l3_on_the_coroutine_runtime_matches_t1_either_way() {
    let t1 = ExecutionCollector::new();
    explore(
        || l3_runtime(false),
        &t1,
        Config::default().collect_errors().with_time_filter(),
    );
    let t1_keys: BTreeSet<String> = t1.terminal_keys().into_iter().collect();

    let (undeclared, _, _) = l3_runtime_run(false);
    let (declared, _, _) = l3_runtime_run(true);
    assert_eq!(
        undeclared, t1_keys,
        "undeclared: T2 realizable set == T1-filter's"
    );
    assert_eq!(
        declared, t1_keys,
        "declared: T2 realizable set == T1-filter's"
    );
}

/// Without a declared future the lookahead cannot force `rg←g`, so the s→r revisit is not
/// rejected and its subtree is fruitless. This is the documented C1-safe cost of `None`
/// (`crate::program::Program::possible_future`), pinned here so it stays a *measured* cost.
#[test]
fn l3_on_the_coroutine_runtime_undeclared_leaves_dead_branches() {
    let (_, dead, visits) = l3_runtime_run(false);
    assert!(
        dead > 0,
        "an undeclared future cannot force rg←g, so Visit(G′) is fruitless (0 of {visits})"
    );
}

/// H1: with the future declared, the forced closure reaches `m` and the gate rejects s→r — the
/// same zero-dead-branch guarantee the table-program L3 regression pins.
#[test]
fn l3_on_the_coroutine_runtime_declared_future_has_no_dead_branches() {
    let (_, dead, visits) = l3_runtime_run(true);
    assert_eq!(
        dead, 0,
        "declared future ⇒ the lookahead rejects s→r (of {visits} visits)"
    );
}

// -- Fix B v2 (C5): value-dependent reproducer (must-expert) --------------------------------

/// The minimal value-dependent reproducer of the refuted-Lemma-2 (C5) loss (`must-expert`): a
/// nondet value gates whether the revisiting send exists / is an early competitor, so the
/// syntactic min-value canonical source is eager-infeasible while a later value holds. Under the
/// **untimed** superset there are 7 terminals; the T1 filter keeps 4; the T2 predicate must also
/// realize **4** (v1/pre-Fix-B gave 2 — the monitor's message reads were lost). This is the
/// value-dependent analogue of the raft `--faults 1` loss, which the value-*independent*
/// `SeqProgram` fuzz structurally cannot build.
fn reproducer() -> must::System {
    use must::{Ctx, System};
    let mut sys = System::new();
    // T0 (coupler): fire a self-timer to advance its clock to 10, then a nondet that (min="alive")
    // emits a *fast* heartbeat which eagerly beats T1's late timer — so T1 never sends "L".
    sys.add(|c: Ctx| async move {
        c.send_within(0, "t0", Model::Asyn, Window::new(10, 10));
        c.recv(|x: &str| x == "t0").await;
        if c.nondet(["alive", "crash"]).await == "alive" {
            c.send_within(1, "hb", Model::Asyn, Window::new(1, 1));
        }
    });
    // T1 (candidate): a late timer [150,150]; reads whichever of {timer, hb} is eagerly available.
    // Only the "timer" reading leads it to send the late "L" that revisits the monitor.
    sys.add(|c: Ctx| async move {
        c.send_within(1, "timer", Model::Asyn, Window::new(150, 150));
        let m = c.recv(|x: &str| x == "timer" || x == "hb").await;
        if m == "timer" {
            c.send(2, "L", Model::Asyn); // untimed [0,∞): a late send, revisits the monitor
        }
    });
    // T2 (monitor): two non-blocking receives that may read "L" (via a backward revisit) or time out.
    sys.add(|c: Ctx| async move {
        c.recv_timeout(|x: &str| x == "L").await;
        c.recv_timeout(|x: &str| x == "L").await;
    });
    sys
}

/// Counts the nondet-arm oracle calls and their verdicts (the "differential canon logger" of
/// T2_ORACLE_SPEC §3.3, distilled into a regression assertion).
#[derive(Default)]
struct ViableStats {
    calls: std::sync::atomic::AtomicUsize,
    rejected: std::sync::atomic::AtomicUsize,
}
impl must::Observer for ViableStats {
    fn on_viable_verdict(
        &self,
        _base: &ExecutionGraph,
        _ep: must::EventId,
        _v: must::Val,
        _revisiting: must::EventId,
        _rev_label: &Label,
        verdict: bool,
    ) {
        use std::sync::atomic::Ordering::Relaxed;
        self.calls.fetch_add(1, Relaxed);
        if !verdict {
            self.rejected.fetch_add(1, Relaxed);
        }
    }
}

#[test]
fn fixb_value_dependent_reproducer_t2_equals_t1() {
    // T1-filter reference (realizable full terminals).
    let t1 = ExecutionCollector::new();
    explore(
        reproducer,
        &t1,
        Config::default().collect_errors().with_time_filter(),
    );
    let t1_keys: BTreeSet<String> = t1.full_keys().into_iter().collect();

    // Zombie arbitration (T2_ORACLE_SPEC §3.2): the untimed walk under the DES order must
    // realize the same set.
    let zb = ExecutionCollector::new();
    explore(
        reproducer,
        &zb,
        Config::default().collect_errors().with_time_zombie(),
    );
    let zb_keys: BTreeSet<String> = zb.full_keys().into_iter().collect();
    assert_eq!(zb_keys, t1_keys, "reproducer: zombie must equal T1-filter");

    // T2 predicate (the PASS oracle): must reproduce the same realizable set, no duplicates.
    let obs = (
        ExecutionCollector::new(),
        (DeadBranchDetector::new(), ViableStats::default()),
    );
    explore(
        reproducer,
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let (t2, (_dead, viable)) = obs;
    let t2_vec = t2.terminal_keys();
    let t2_keys: BTreeSet<String> = t2_vec.iter().cloned().collect();
    assert_eq!(
        t2_vec.len(),
        t2_keys.len(),
        "reproducer: T2 duplicate terminals"
    );
    let t2_full: BTreeSet<String> = t2.full_keys().into_iter().collect();
    assert_eq!(
        t2_full, t1_keys,
        "reproducer: T2 realizable full keys must equal the T1-filter reference (Fix B C5)"
    );

    // The false path of the existential oracle is load-bearing here: the crash-branch holder
    // ("crash" > "alive") PASSes only because viable("alive") is refuted — under "alive" the
    // fast heartbeat eagerly beats the late timer, so the revisiting "L" send never exists.
    // A canon that spuriously calls smaller values viable would reject this revisit and lose
    // realizable terminals (the raft --faults 1 class).
    use std::sync::atomic::Ordering::Relaxed;
    assert!(
        viable.calls.load(Relaxed) > 0,
        "reproducer: the PASS oracle must be exercised (a non-min holder is tested)"
    );
    assert!(
        viable.rejected.load(Relaxed) > 0,
        "reproducer: viable(\"alive\") must be refuted (the false path is load-bearing)"
    );
}

// -- The --bug=108 class: a min-holder PASS through a two-hop revisit (T2_ORACLE_SPEC §3.3) --

/// Minimized regression of the raft `--bug --timeouts 100,105,200` 92-vs-108 loss class. The
/// four §3.3 ingredients:
///   1. a **two-hop late chain** (T2's `g`[5,5] → T1: `recv(=g); send v` → T0), whose events
///      enter the graph only after the victim's read;
///   2. a **consumed competitor**: T0's early self-timer `t0`[1,1] is consumed by a po-earlier
///      receive, keeping the late core chain feasible;
///   3. a **tested nondet in Deleted, outside prefix(s)**: T2's `q`-chain nondet fires at 2 —
///      after the monitor's ⊥-read, causally independent of the `L` chain — so the revisit of
///      the monitor deletes it and `RevisitCondition` tests it;
///   4. the deleted nondet holds its **min** value, so the PASS rule accepts with **zero**
///      oracle calls — exactly how the 108 errors were restored (every raft rejection held
///      min). The old replay canon re-derived the deleted region by a forward replay and could
///      spuriously diverge on revisit-established reads; the graph-is-its-own-witness rule
///      cannot.
fn bug_class_program() -> must::System {
    use must::{Ctx, System};
    let mut sys = System::new();
    // T0 (core): consume the early timer (ingredient 2), then read the relay's late `v`
    // (the only matching source), then announce `L` — the send that revisits the monitor.
    sys.add(|c: Ctx| async move {
        c.send_within(0, "t0", Model::Asyn, Window::new(1, 1));
        c.recv(|x: &str| x == "t0").await;
        let m = c.recv(|x: &str| x == "v").await;
        if m == "v" {
            c.send(3, "L", Model::Asyn); // [0,∞): the monitor is time-transparent
        }
    });
    // T1 (relay, hop 2): woken at 5 by `g`, then its `v` reaches T0 — a late send by
    // construction (po-after a receive that fires at 5).
    sys.add(|c: Ctx| async move {
        c.recv(|x: &str| x == "g").await;
        c.send_within(0, "v", Model::Asyn, Window::new(0, 0));
    });
    // T2 (hop 1 + the deleted nondet carrier): feed the relay, then a self-timer chain whose
    // nondet fires at 2 — po-after a blocking receive, causally independent of the `L` chain.
    sys.add(|c: Ctx| async move {
        c.send_within(1, "g", Model::Asyn, Window::new(5, 5));
        c.send_within(2, "q", Model::Asyn, Window::new(2, 2));
        c.recv(|x: &str| x == "q").await;
        c.nondet(["m", "z"]).await;
    });
    // T3 (monitor): reads `L` via the backward revisit, or times out.
    sys.add(|c: Ctx| async move {
        c.recv_timeout(|x: &str| x == "L").await;
    });
    sys
}

#[test]
fn bug_class_min_holder_revisit_survives() {
    // T1-filter reference.
    let t1 = ExecutionCollector::new();
    explore(
        bug_class_program,
        &t1,
        Config::default().collect_errors().with_time_filter(),
    );
    let t1_keys: BTreeSet<String> = t1.full_keys().into_iter().collect();

    // Zombie arbitration.
    let zb = ExecutionCollector::new();
    explore(
        bug_class_program,
        &zb,
        Config::default().collect_errors().with_time_zombie(),
    );
    let zb_keys: BTreeSet<String> = zb.full_keys().into_iter().collect();
    assert_eq!(zb_keys, t1_keys, "bug-class: zombie must equal T1-filter");

    // T2 predicate: same realizable set (both monitor variants — the ⊥ timeout and the
    // revisit-established `L` read), no duplicates. Oracle traffic: the min-holder ("m")
    // branch hosts the revisit with zero calls (the PASS short-circuit — how the 108 errors
    // were restored), while the sibling "z" branch consults the oracle once and finds "m"
    // viable (the q-chain is causally independent of `L`), correctly deduplicating the
    // revisit into the min branch — so calls happen but none is a rejection.
    let obs = (ExecutionCollector::new(), ViableStats::default());
    explore(
        bug_class_program,
        &obs,
        Config::default().collect_errors().with_time_predicate(),
    );
    let (t2, viable) = obs;
    let t2_vec = t2.terminal_keys();
    let t2_keys: BTreeSet<String> = t2_vec.iter().cloned().collect();
    assert_eq!(
        t2_vec.len(),
        t2_keys.len(),
        "bug-class: T2 duplicate terminals"
    );
    let t2_full: BTreeSet<String> = t2.full_keys().into_iter().collect();
    assert_eq!(
        t2_full, t1_keys,
        "bug-class: T2 must keep the revisit-established monitor read (the 92-vs-108 loss)"
    );
    assert!(
        t1_keys.len() >= 2,
        "bug-class: both monitor variants must be realizable (got {})",
        t1_keys.len()
    );
    use std::sync::atomic::Ordering::Relaxed;
    assert!(
        viable.calls.load(Relaxed) >= 1,
        "bug-class: the non-min sibling must consult the oracle"
    );
    assert_eq!(
        viable.rejected.load(Relaxed),
        0,
        "bug-class: viable(\"m\") must hold (the q-chain is independent of the L chain), so \
         the non-min sibling defers to the min branch and no verdict is a rejection"
    );
}
