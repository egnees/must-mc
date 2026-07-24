//! Consistency tests on hand-built graphs. Each example is built at the label level;
//! sends are tagged with the model under test, while receives carry no model.

use must::consistency::{
    consistent, consistent_asyn, consistent_cd, consistent_mbox, consistent_p2p, well_formed,
};
use must::event::{Label, Model, Pred};
use must::graph::ExecutionGraph;

fn recv(pred: Pred) -> Label {
    Label::recv(pred)
}

// ---------------------------------------------------------------------------
// Well-formedness
// ---------------------------------------------------------------------------

#[test]
fn double_read_is_ill_formed() {
    // Two receives reading the same send violate rf-inverse functionality (Def 3.3.3).
    let mut g = ExecutionGraph::new();
    let s = g.add_event(0, Label::send(Model::Asyn, 1, "1"));
    let r1 = g.add_event(1, recv(Pred::any()));
    let r2 = g.add_event(1, recv(Pred::any()));
    g.set_rf(r1, Some(s));
    g.set_rf(r2, Some(s));
    assert!(!well_formed(&g));
    assert!(!consistent(&g));
}

#[test]
fn predicate_mismatch_is_ill_formed() {
    // rf must connect matching send/receive (Def 3.3.4): val(s) in vals(r).
    let mut g = ExecutionGraph::new();
    let s = g.add_event(0, Label::send(Model::Asyn, 1, "1"));
    let r = g.add_event(1, recv(Pred::eq("2")));
    g.set_rf(r, Some(s));
    assert!(!well_formed(&g));
}

#[test]
fn causal_cycle_is_ill_formed_under_every_model() {
    // e0 reads e3, e2 reads e1: porf runs e0->e1->e2->e3->e0 (Def 3.3.5, No-OOTA).
    let mut g = ExecutionGraph::new();
    let e0 = g.add_event(0, recv(Pred::any()));
    let e1 = g.add_event(0, Label::send(Model::Asyn, 1, "b"));
    let e2 = g.add_event(1, recv(Pred::any()));
    let e3 = g.add_event(1, Label::send(Model::Asyn, 0, "a"));
    g.set_rf(e0, Some(e3));
    g.set_rf(e2, Some(e1));
    assert!(!well_formed(&g));
    // consistent() rejects it under every model (asyn included) because it checks
    // well-formedness first, even though consistent_asyn itself is trivially true.
    assert!(consistent_asyn(&g));
    assert!(!consistent(&g));
}

// ---------------------------------------------------------------------------
// Example 2.8 - selective receives accept out-of-order delivery under p2p.
// ---------------------------------------------------------------------------

#[test]
fn example_2_8_p2p_consistent() {
    // T1: send(T2,1); send(T2,2)   T2: recv(x=2); recv(x=1)
    let mut g = ExecutionGraph::new();
    let s1 = g.add_event(0, Label::send(Model::P2p, 1, "1"));
    let s2 = g.add_event(0, Label::send(Model::P2p, 1, "2"));
    let r2 = g.add_event(1, recv(Pred::eq("2")));
    let r1 = g.add_event(1, recv(Pred::eq("1")));
    g.set_rf(r2, Some(s2));
    g.set_rf(r1, Some(s1));
    assert!(consistent(&g));
    assert!(consistent_p2p(&g));
}

// ---------------------------------------------------------------------------
// Example 3.1 - graph (1) consistent everywhere, graph (2) p2p-yes/cd-no/mbox-no.
// ---------------------------------------------------------------------------

/// `T1: send(T3,1); send(T2,2)  ||  T2: recv(); send(T3,3)  ||  T3: recv(); recv()`.
/// `crossed = true` builds graph (2): T3 reads 3 then 1.
fn example_3_1(model: Model, crossed: bool) -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let s_t3_1 = g.add_event(0, Label::send(model, 2, "1")); // S(T3,1)
    let s_t2_2 = g.add_event(0, Label::send(model, 1, "2")); // S(T2,2)
    let r_t2 = g.add_event(1, recv(Pred::any()));
    let s_t3_3 = g.add_event(1, Label::send(model, 2, "3")); // S(T3,3)
    let r_t3_a = g.add_event(2, recv(Pred::any()));
    let r_t3_b = g.add_event(2, recv(Pred::any()));
    g.set_rf(r_t2, Some(s_t2_2));
    if crossed {
        g.set_rf(r_t3_a, Some(s_t3_3));
        g.set_rf(r_t3_b, Some(s_t3_1));
    } else {
        g.set_rf(r_t3_a, Some(s_t3_1));
        g.set_rf(r_t3_b, Some(s_t3_3));
    }
    g
}

#[test]
fn example_3_1_natural_consistent_everywhere() {
    for model in [Model::P2p, Model::Cd, Model::Mbox, Model::Asyn] {
        assert!(consistent(&example_3_1(model, false)), "model {model}");
    }
}

#[test]
fn example_3_1_crossed_p2p_yes_cd_no_mbox_no() {
    assert!(consistent(&example_3_1(Model::P2p, true)));
    assert!(consistent(&example_3_1(Model::Asyn, true)));
    assert!(!consistent(&example_3_1(Model::Cd, true)));
    assert!(!consistent(&example_3_1(Model::Mbox, true)));

    // Same conclusions via the per-model predicates directly.
    assert!(!consistent_cd(&example_3_1(Model::Cd, true)));
    assert!(!consistent_mbox(&example_3_1(Model::Mbox, true)));
}

// ---------------------------------------------------------------------------
// p2p clauses (b) and (c).
// ---------------------------------------------------------------------------

#[test]
fn p2p_clause_b_forbids_jumping_over_an_earlier_pending_send() {
    // T1: send(T2,1); send(T2,2)   T2: recv()  reading 2, leaving 1 unread earlier.
    let mut g = ExecutionGraph::new();
    let _s1 = g.add_event(0, Label::send(Model::P2p, 1, "1"));
    let s2 = g.add_event(0, Label::send(Model::P2p, 1, "2"));
    let r = g.add_event(1, recv(Pred::any()));
    g.set_rf(r, Some(s2));
    assert!(!consistent_p2p(&g));
    assert!(!consistent(&g));
    // asyn imposes no ordering.
    let mut ga = ExecutionGraph::new();
    let _a1 = ga.add_event(0, Label::send(Model::Asyn, 1, "1"));
    let a2 = ga.add_event(0, Label::send(Model::Asyn, 1, "2"));
    let ra = ga.add_event(1, recv(Pred::any()));
    ga.set_rf(ra, Some(a2));
    assert!(consistent(&ga));
}

#[test]
fn p2p_clause_b_allows_skipping_earlier_send_that_does_not_match() {
    // T1: send(T2,1); send(T2,2)   T2: recv(x=2) reads s2; s1 stays unread but does
    // NOT satisfy the predicate, so clause (b) must not fire (its intersection with
    // mval is what makes this consistent - dropping `matches` from (b) fails this test).
    let mut g = ExecutionGraph::new();
    let _s1 = g.add_event(0, Label::send(Model::P2p, 1, "1"));
    let s2 = g.add_event(0, Label::send(Model::P2p, 1, "2"));
    let r = g.add_event(1, recv(Pred::eq("2")));
    g.set_rf(r, Some(s2));
    assert!(consistent_p2p(&g));
    assert!(consistent(&g));
}

#[test]
fn p2p_clause_c_forbids_receiving_same_source_out_of_order() {
    // T1: send(T2,1); send(T2,2)   T2: recv(); recv()  crossed, non-selective.
    let mut g = ExecutionGraph::new();
    let s1 = g.add_event(0, Label::send(Model::P2p, 1, "1"));
    let s2 = g.add_event(0, Label::send(Model::P2p, 1, "2"));
    let ra = g.add_event(1, recv(Pred::any()));
    let rb = g.add_event(1, recv(Pred::any()));
    g.set_rf(ra, Some(s2));
    g.set_rf(rb, Some(s1));
    assert!(!consistent_p2p(&g));
}

// ---------------------------------------------------------------------------
// send(T2,1); send(T2,2) || recv(); recv() - mbox rule B regression.
// ---------------------------------------------------------------------------

/// `crossed = true`: T2 reads 2 then 1.
fn m1(model: Model, crossed: bool) -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let s1 = g.add_event(0, Label::send(model, 1, "1"));
    let s2 = g.add_event(0, Label::send(model, 1, "2"));
    let ra = g.add_event(1, recv(Pred::any()));
    let rb = g.add_event(1, recv(Pred::any()));
    if crossed {
        g.set_rf(ra, Some(s2));
        g.set_rf(rb, Some(s1));
    } else {
        g.set_rf(ra, Some(s1));
        g.set_rf(rb, Some(s2));
    }
    g
}

#[test]
fn m1_natural_is_consistent_everywhere() {
    for model in [Model::P2p, Model::Cd, Model::Mbox, Model::Asyn] {
        assert!(consistent(&m1(model, false)), "model {model}");
    }
}

#[test]
fn m1_crossed_only_asyn() {
    assert!(consistent(&m1(Model::Asyn, true)));
    assert!(!consistent(&m1(Model::P2p, true)));
    assert!(!consistent(&m1(Model::Cd, true)));
    assert!(!consistent_mbox(&m1(Model::Mbox, true)));
}

// ---------------------------------------------------------------------------
// Rule A + porf. Two sends can reach T3; reading the causally-later one is
// forbidden under cd and mbox but allowed under p2p.
// ---------------------------------------------------------------------------

/// `T1: send(T3,1); send(T2,go)  ||  T2: recv(); send(T3,2)  ||  T3: recv()`.
/// `read_late = true`: T3 reads the causally-later S(T3,2).
fn m3(model: Model, read_late: bool) -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let s_t3_1 = g.add_event(0, Label::send(model, 2, "1")); // S(T3,1)
    let s_t2_go = g.add_event(0, Label::send(model, 1, "go")); // S(T2,go)
    let r_t2 = g.add_event(1, recv(Pred::any()));
    let s_t3_2 = g.add_event(1, Label::send(model, 2, "2")); // S(T3,2), causally after go
    let r_t3 = g.add_event(2, recv(Pred::any()));
    g.set_rf(r_t2, Some(s_t2_go));
    g.set_rf(
        r_t3,
        if read_late {
            Some(s_t3_2)
        } else {
            Some(s_t3_1)
        },
    );
    g
}

#[test]
fn m3_reading_early_is_consistent_everywhere() {
    for model in [Model::P2p, Model::Cd, Model::Mbox, Model::Asyn] {
        assert!(consistent(&m3(model, false)), "model {model}");
    }
}

#[test]
fn m3_reading_late_p2p_yes_cd_no_mbox_no() {
    assert!(consistent(&m3(Model::P2p, true)));
    assert!(consistent(&m3(Model::Asyn, true)));
    assert!(!consistent(&m3(Model::Cd, true)));
    assert!(!consistent(&m3(Model::Mbox, true)));
}

// ---------------------------------------------------------------------------
// A mbox cycle that runs through *two* mailboxes. A per-destination check would
// miss it; the global digraph over the A, B, C edge sets catches it.
// ---------------------------------------------------------------------------

/// `T1: send(T3,a1); send(T4,b1) || T2: send(T4,b2); send(T3,a2) || T3: recv() x2 || T4: recv() x2`.
/// `crossed = true` builds the cross-mailbox cycle (T3 reads a2 then a1; T4 reads
/// b1 then b2).
fn xchg(model: Model, crossed: bool) -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let a1 = g.add_event(0, Label::send(model, 2, "a1")); // T1 -> T3
    let b1 = g.add_event(0, Label::send(model, 3, "b1")); // T1 -> T4
    let b2 = g.add_event(1, Label::send(model, 3, "b2")); // T2 -> T4
    let a2 = g.add_event(1, Label::send(model, 2, "a2")); // T2 -> T3
    let t3_1 = g.add_event(2, recv(Pred::any()));
    let t3_2 = g.add_event(2, recv(Pred::any()));
    let t4_1 = g.add_event(3, recv(Pred::any()));
    let t4_2 = g.add_event(3, recv(Pred::any()));
    if crossed {
        g.set_rf(t3_1, Some(a2));
        g.set_rf(t3_2, Some(a1));
        g.set_rf(t4_1, Some(b1));
        g.set_rf(t4_2, Some(b2));
    } else {
        g.set_rf(t3_1, Some(a1));
        g.set_rf(t3_2, Some(a2));
        g.set_rf(t4_1, Some(b1));
        g.set_rf(t4_2, Some(b2));
    }
    g
}

#[test]
fn xchg_cross_mailbox_cycle_is_mbox_inconsistent_but_p2p_consistent() {
    // The crossed graph has no single-mailbox cycle, so p2p (which orders only
    // per-sender) accepts it, but the global mbox digraph has an e0->e1->e2->e3->e0 cycle.
    assert!(consistent(&xchg(Model::P2p, true)));
    assert!(!consistent(&xchg(Model::Mbox, true)));
    assert!(!consistent_mbox(&xchg(Model::Mbox, true)));
}

#[test]
fn xchg_natural_is_mbox_consistent() {
    assert!(consistent(&xchg(Model::Mbox, false)));
    assert!(consistent_mbox(&xchg(Model::Mbox, false)));
}

// ---------------------------------------------------------------------------
// Mixed models: a p2p send and an asyn send to the same destination. Pure p2p
// would forbid the crossed reading; the mixed graph allows it.
// ---------------------------------------------------------------------------

fn two_sends_two_recvs(m0: Model, m1_: Model, crossed: bool) -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let s0 = g.add_event(0, Label::send(m0, 1, "1"));
    let s1 = g.add_event(0, Label::send(m1_, 1, "2"));
    let ra = g.add_event(1, recv(Pred::any()));
    let rb = g.add_event(1, recv(Pred::any()));
    if crossed {
        g.set_rf(ra, Some(s1));
        g.set_rf(rb, Some(s0));
    } else {
        g.set_rf(ra, Some(s0));
        g.set_rf(rb, Some(s1));
    }
    g
}

#[test]
fn mixed_p2p_asyn_allows_crossed_reading() {
    // Mixed: only the p2p send is constrained, and it is read by the later receive,
    // so both orderings are consistent - two executions instead of one.
    assert!(consistent(&two_sends_two_recvs(
        Model::P2p,
        Model::Asyn,
        false
    )));
    assert!(consistent(&two_sends_two_recvs(
        Model::P2p,
        Model::Asyn,
        true
    )));
    // Pure p2p forbids the crossed reading (clause (c)).
    assert!(!consistent(&two_sends_two_recvs(
        Model::P2p,
        Model::P2p,
        true
    )));
}
