//! Per-model execution-count oracles. Each program is parameterised by the communication
//! [`Model`] so the same shape is checked under asyn/p2p/cd/mbox; the expected counts show
//! how much each model constrains delivery.
//!
//! Thread numbering: the paper's 1-based `T1/T2/...` are the 0-based tids `0/1/...` here,
//! and every `send(k, ...)` argument is already the 0-based destination.

mod common;

use common::{assert_oracle, permutations, recv, send, SeqProgram};
use must::event::Model;

const MODELS: [Model; 4] = [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox];

/// Look up the expected full-execution count for `model` from `(asyn, p2p, cd, mbox)`.
fn expected(model: Model, counts: (usize, usize, usize, usize)) -> usize {
    match model {
        Model::Asyn => counts.0,
        Model::P2p => counts.1,
        Model::Cd => counts.2,
        Model::Mbox => counts.3,
    }
}

// -- Example 3.1 ------------------------------------------------------------------

/// `T0: send(2,"1"); send(1,"2") || T1: recv(); send(2,"3") || T2: recv(); recv()`.
/// T2 receives both "1" (from T0) and "3" (from T1). Under cd/mbox "3" is causally after
/// "1", so it must arrive second: 1 graph. Under asyn/p2p the two sends have different
/// senders, so both orders survive: 2.
fn example_3_1(model: Model) -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(model, 2, "1"), send(model, 1, "2")],
        vec![recv(), send(model, 2, "3")],
        vec![recv(), recv()],
    ])
}

#[test]
fn example_3_1_all_models() {
    for model in MODELS {
        let e = expected(model, (2, 2, 1, 1));
        assert_oracle(
            &format!("Example 3.1 [{model}]"),
            &example_3_1(model),
            &permutations(3),
            e,
            0,
        );
    }
}

// -- Two same-sender messages, two receives ---------------------------------------

/// `T0: send(1,"1"); send(1,"2") || T1: recv(); recv()`. Same sender to the same
/// receiver: p2p/cd/mbox force send order ("1" then "2") -- 1 graph; asyn allows both
/// orders -- 2. Exercises mbox's same-sender rule without a porf edge.
fn m1(model: Model) -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(model, 1, "1"), send(model, 1, "2")],
        vec![recv(), recv()],
    ])
}

#[test]
fn m1_all_models() {
    for model in MODELS {
        let e = expected(model, (2, 1, 1, 1));
        assert_oracle(&format!("M1 [{model}]"), &m1(model), &permutations(2), e, 0);
    }
}

// -- One receive, a causally-ordered pair of sends --------------------------------

/// `T0: send(2,"1"); send(1,"go") || T1: recv(); send(2,"2") || T2: recv()`.
/// T2's single receive may read "1" (from T0) or "2" (from T1). Under cd/mbox "2" is
/// causally after "1", and reading "2" while "1" is unread is inconsistent: 1 graph.
/// Under asyn/p2p the two sends have different senders: 2.
fn m3(model: Model) -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(model, 2, "1"), send(model, 1, "go")],
        vec![recv(), send(model, 2, "2")],
        vec![recv()],
    ])
}

#[test]
fn m3_all_models() {
    for model in MODELS {
        let e = expected(model, (2, 2, 1, 1));
        assert_oracle(&format!("M3 [{model}]"), &m3(model), &permutations(3), e, 0);
    }
}

// -- XCHG: a cross-mailbox mbox cycle ---------------------------------------------

/// `T0: send(2,"a1"); send(3,"b1") || T1: send(3,"b2"); send(2,"a2") ||
///  T2: recv(); recv() || T3: recv(); recv()`. Under mbox the global enqueue order across
/// the two mailboxes (tids 2 and 3) forbids one of the four otherwise-independent
/// orderings: 3 instead of 4 -- the case a per-destination mbox check would miss.
fn xchg(model: Model) -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(model, 2, "a1"), send(model, 3, "b1")],
        vec![send(model, 3, "b2"), send(model, 2, "a2")],
        vec![recv(), recv()],
        vec![recv(), recv()],
    ])
}

#[test]
fn xchg_all_models() {
    for model in MODELS {
        let e = expected(model, (4, 4, 4, 3));
        assert_oracle(
            &format!("XCHG [{model}]"),
            &xchg(model),
            &permutations(4),
            e,
            0,
        );
    }
}

// -- A1: repeated revisit of one receive ------------------------------------------

/// `T0: recv() || T1: send(0,"a"); send(0,"b") || T2: send(0,"c")`. The single receive
/// may read any of a/b/c under asyn (3); under p2p/cd/mbox reading "b" while the earlier
/// same-sender "a" is unread is inconsistent, so only a or c (2). Under asyn this stresses
/// repeated backward revisits of one receive, which p2p masks -- hence all permutations.
fn a1(model: Model) -> SeqProgram {
    SeqProgram::new(vec![
        vec![recv()],
        vec![send(model, 0, "a"), send(model, 0, "b")],
        vec![send(model, 0, "c")],
    ])
}

#[test]
fn a1_all_models_all_permutations() {
    for model in MODELS {
        let e = expected(model, (3, 2, 2, 2));
        assert_oracle(&format!("A1 [{model}]"), &a1(model), &permutations(3), e, 0);
    }
}

// -- Mixed models to one destination ----------------------------------------------

/// `T0: send(1,"1", P2p); send(1,"2", Asyn) || T1: recv(); recv()`. The second send is
/// asyn, so p2p's send-order constraint does not apply between the two: both delivery
/// orders survive -- 2 executions, where pure p2p would give 1. Each model's consistency
/// ranges only over that model's own sends.
#[test]
fn mixed_models_to_one_destination() {
    let prog = SeqProgram::new(vec![
        vec![send(Model::P2p, 1, "1"), send(Model::Asyn, 1, "2")],
        vec![recv(), recv()],
    ]);
    assert_oracle("mixed p2p+asyn", &prog, &permutations(2), 2, 0);
}
