//! Integration tests for the forced-closure gate (T-FC, T2_PLAN §4 / §5.2).
//!
//! The headline case is the L3 counterexample (TIME_PLAN "Дорожная карта T2"): a graph `G′`
//! that is eager-feasible on its own but whose *obligatory* forward continuation is
//! eager-infeasible, so a backward revisit landing on it must be rejected. A T1-style
//! terminal-count check is blind to this (the terminal sets coincide); the forced-closure
//! lookahead is the object that sees it.
//!
//! Every verdict is cross-checked against `common::time_feasible_ref` — the independent
//! integer-enumeration reference for the eager semantics (no solver) — applied to the closure
//! graph the gate actually builds.

mod common;

use common::{recv, recv_eq, time_feasible_ref, SeqProgram};
use must::event::{EventId, Label, Model, Window};
use must::time::{forced_closure, forced_closure_feasible};
use must::{check, ExecutionGraph};

const ASYN: Model = Model::Asyn;

/// A send with a finite delivery window `[lo, hi]`.
fn tsend(dst: usize, v: &str, lo: u64, hi: u64) -> Label {
    Label::send_within(ASYN, dst, v, Window::new(lo, hi))
}

/// The 6-thread L3 program (TIME_PLAN "Контрпример"):
/// ```text
/// T0: r  = recv(any)
/// T1: a  = send(T0,"a",[1,100])
/// T2: rg = recv(=g);  m = send(T0,"b0",[0,0])
/// T3: g  = send(T2,"g",[5,5])
/// T4: rs = recv(=x);  s = send(T0,"b", [0,0])
/// T5: x  = send(T4,"x",[30,30])
/// ```
fn l3_program() -> SeqProgram {
    SeqProgram::new(vec![
        vec![recv()],                             // T0
        vec![tsend(0, "a", 1, 100)],              // T1
        vec![recv_eq("g"), tsend(0, "b0", 0, 0)], // T2
        vec![tsend(2, "g", 5, 5)],                // T3
        vec![recv_eq("x"), tsend(0, "b", 0, 0)],  // T4
        vec![tsend(4, "x", 30, 30)],              // T5
    ])
}

/// `G′ = {a, g, x, r←s, rs←x, s}` — the result of the revisit `s → r` after `restrict`
/// (`m` and `rg` deleted, T2 left empty).
fn g_prime() -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let r = g.add_event(0, recv());
    let _a = g.add_event(1, tsend(0, "a", 1, 100));
    let _gg = g.add_event(3, tsend(2, "g", 5, 5));
    let rs = g.add_event(4, recv_eq("x"));
    let s = g.add_event(4, tsend(0, "b", 0, 0));
    let x = g.add_event(5, tsend(4, "x", 30, 30));
    g.set_rf(r, Some(s));
    g.set_rf(rs, Some(x));
    g
}

/// A full terminal of the L3 program in which `r` reads the send with payload `which`
/// (`"a"` = a, `"b0"` = m, `"b"` = s); `rg←g`, `rs←x` are forced/selective.
fn l3_terminal(which: &str) -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let r = g.add_event(0, recv());
    let a = g.add_event(1, tsend(0, "a", 1, 100));
    let rg = g.add_event(2, recv_eq("g"));
    let m = g.add_event(2, tsend(0, "b0", 0, 0));
    let gg = g.add_event(3, tsend(2, "g", 5, 5));
    let rs = g.add_event(4, recv_eq("x"));
    let s = g.add_event(4, tsend(0, "b", 0, 0));
    let x = g.add_event(5, tsend(4, "x", 30, 30));
    g.set_rf(rg, Some(gg));
    g.set_rf(rs, Some(x));
    let src = match which {
        "a" => a,
        "b0" => m,
        "b" => s,
        other => panic!("no send with payload {other}"),
    };
    g.set_rf(r, Some(src));
    g
}

/// Assert `forced_closure_feasible(g0)` equals both `check(closure)` and the independent
/// integer reference on the closure; return the verdict.
fn gated_verdict(g0: &ExecutionGraph, prog: &SeqProgram, prio: &[usize]) -> bool {
    let closure = forced_closure(g0, prog, prio);
    let verdict = forced_closure_feasible(g0, prog, prio);
    assert_eq!(
        verdict,
        check(&closure).is_feasible(),
        "forced_closure_feasible must equal check(closure)"
    );
    let mut budget = 5_000_000usize;
    let reference = time_feasible_ref(&closure, &mut budget).expect("closure within ref budget");
    assert_eq!(
        verdict, reference,
        "forced-closure verdict disagrees with the integer reference"
    );
    verdict
}

#[test]
fn l3_revisit_is_rejected() {
    let prog = l3_program();
    let prio: Vec<usize> = (0..6).collect();
    let g = g_prime();

    // G′ is untimed-consistent and eager-feasible on its own (arr(a) stretches to 30)...
    assert!(check(&g).is_feasible(), "G′ alone is eager-feasible");

    // ...but the closure re-adds the obligatory rg←g and m.
    let closure = forced_closure(&g, &prog, &prio);
    assert!(closure.contains(EventId::new(2, 0)), "rg is forced back in");
    assert!(closure.contains(EventId::new(2, 1)), "m is forced back in");
    assert_eq!(
        closure.reads_from(EventId::new(2, 0)),
        Some(EventId::new(3, 0)),
        "rg reads g"
    );

    // The closure is infeasible (avail(m)=5 ≥ avail(s)=30 is false) ⇒ the revisit is rejected.
    assert!(
        !gated_verdict(&g, &prog, &prio),
        "L3: forced_closure(G′) is infeasible, so the revisit s→r must be rejected"
    );
}

#[test]
fn l3_terminals_realizable_split() {
    let prog = l3_program();
    let prio: Vec<usize> = (0..6).collect();

    // r←a and r←m are realizable full terminals; their forced-closure = themselves.
    assert!(
        gated_verdict(&l3_terminal("a"), &prog, &prio),
        "r←a realizable"
    );
    assert!(
        gated_verdict(&l3_terminal("b0"), &prog, &prio),
        "r←m realizable"
    );

    // The full r←s is infeasible by itself (competitor m=5 < avail(s)=30).
    let ts = l3_terminal("b");
    assert!(!check(&ts).is_feasible(), "the full r←s is time-infeasible");
    assert!(!gated_verdict(&ts, &prog, &prio), "r←s not realizable");
}

/// C2 (T2_PLAN §6): the forced-closure *verdict* is conjectured independent of the
/// deterministic thread-visit order. A failure here would signal C2 is false (escalate to
/// must-expert), not a coding bug. Checked on G′ and the three L3 terminals across a spread of
/// 6-thread priority permutations.
#[test]
fn forced_closure_verdict_is_order_independent() {
    let prog = l3_program();
    let orders: Vec<Vec<usize>> = vec![
        (0..6).collect(),
        (0..6).rev().collect(),
        vec![2, 3, 4, 5, 0, 1],
        vec![5, 0, 4, 1, 3, 2],
        vec![3, 1, 4, 0, 5, 2],
    ];
    let graphs = [
        ("G′", g_prime(), false),
        ("r←a", l3_terminal("a"), true),
        ("r←m", l3_terminal("b0"), true),
        ("r←s", l3_terminal("b"), false),
    ];
    for (name, g, expected) in &graphs {
        for order in &orders {
            assert_eq!(
                forced_closure_feasible(g, &prog, order),
                *expected,
                "{name}: verdict changed under visit order {order:?}"
            );
        }
    }
}

/// A blocking receive with two distinct matching senders is a real rf-fork: the forced-closure
/// stops before it (adds neither the receive nor a spurious source).
#[test]
fn forced_closure_stops_at_rf_fork() {
    // Finite windows so the integer reference applies; the point is the fork, not the timing.
    let prog = SeqProgram::new(vec![
        vec![tsend(2, "a", 0, 10)],
        vec![tsend(2, "b", 0, 10)],
        vec![recv()],
    ]);
    let mut g0 = ExecutionGraph::new();
    g0.add_event(0, tsend(2, "a", 0, 10));
    g0.add_event(1, tsend(2, "b", 0, 10));
    let prio = [0, 1, 2];
    let closure = forced_closure(&g0, &prog, &prio);
    assert!(
        !closure.contains(EventId::new(2, 0)),
        "the contested receive is not forced"
    );
    assert!(
        gated_verdict(&g0, &prog, &prio),
        "no receive ⇒ vacuously feasible"
    );
}

/// C1 regression (must-expert): a blocking receive whose source is unique only *because a
/// competitor is hidden behind an unforced receive* must NOT be forced — else the gate
/// over-prunes the realizable terminal `r←m, r2←S`.
/// ```text
/// T0: r=recv(=v); r2=recv(=v)      T1: S=send(T0,"v",[30,30])
/// T2: rk=recv(=k); m=send(T0,"v",[1,1])   T3: k=send(T2,"k",[0,0])
/// ```
#[test]
fn c1_hidden_competitor_is_not_over_pruned() {
    let prog = SeqProgram::new(vec![
        vec![recv_eq("v"), recv_eq("v")],
        vec![tsend(0, "v", 30, 30)],
        vec![recv_eq("k"), tsend(0, "v", 1, 1)],
        vec![tsend(2, "k", 0, 0)],
    ]);
    let empty = ExecutionGraph::new();
    let prio = [0, 1, 2, 3];

    // r must not be forced (S has a hidden competitor m and a second consumer r2).
    let closure = forced_closure(&empty, &prog, &prio);
    assert_eq!(
        closure.thread_len(0),
        0,
        "the C1-unsafe receive r is not forced"
    );

    // The gate must NOT reject Visit(∅) — its verdict agrees with the integer reference on the
    // closure, and it is feasible because the subtree holds a realizable terminal.
    assert!(
        gated_verdict(&empty, &prog, &prio),
        "C1: the gate must not over-prune"
    );

    // That realizable terminal (r←m, r2←S) exists — confirm with the integer reference.
    let mut term = ExecutionGraph::new();
    let r = term.add_event(0, recv_eq("v"));
    let r2 = term.add_event(0, recv_eq("v"));
    let s_big = term.add_event(1, tsend(0, "v", 30, 30));
    let rk = term.add_event(2, recv_eq("k"));
    let m = term.add_event(2, tsend(0, "v", 1, 1));
    let k = term.add_event(3, tsend(2, "k", 0, 0));
    term.set_rf(rk, Some(k));
    term.set_rf(r, Some(m));
    term.set_rf(r2, Some(s_big));
    let mut budget = 5_000_000usize;
    assert_eq!(
        time_feasible_ref(&term, &mut budget),
        Some(true),
        "r←m, r2←S is realizable — the gate would be wrong to prune the subtree"
    );
}
