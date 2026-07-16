//! Differential test: a parallel `explore` must produce exactly the same executions as the
//! sequential one - same full/blocked/error counts and the same *set* of canonical
//! `(E, po, rf)` keys - across a range of worker counts. The parallel split reorders the
//! executions but must not add, drop, or duplicate any (Theorem 4.1). This is the primary
//! guard on the parallel driver; the sequential path is already covered by the oracle and
//! fuzz suites.

mod common;

use common::{nondet, recv, recv_eq, recv_nb, send, SeqProgram};
use must::event::Model;
use must::{explore, Config, ExecutionCollector, Program};

const P2P: Model = Model::P2p;

fn sorted(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v
}

/// Assert a parallel `explore` matches the sequential one for every worker count in
/// `1, 2, 3, 6` (1 exercises the queue with no real parallelism; 6 stresses several
/// workers at once). `make` rebuilds the program per worker (the runtime is not `Send`).
fn check<P: Program>(name: &str, cfg: Config, make: impl Fn() -> P + Sync) {
    let seq = ExecutionCollector::new();
    explore(&make, &seq, cfg.clone().with_threads(1));
    for threads in [1usize, 2, 3, 6] {
        let par = ExecutionCollector::new();
        explore(&make, &par, cfg.clone().with_threads(threads));
        assert_eq!(
            par.full_count(),
            seq.full_count(),
            "{name}: full count @ {threads} threads"
        );
        assert_eq!(
            par.blocked_count(),
            seq.blocked_count(),
            "{name}: blocked count @ {threads} threads"
        );
        assert_eq!(
            par.error_count(),
            seq.error_count(),
            "{name}: error count @ {threads} threads"
        );
        assert_eq!(
            sorted(par.terminal_keys()),
            sorted(seq.terminal_keys()),
            "{name}: terminal key set @ {threads} threads"
        );
        assert_eq!(
            sorted(par.error_keys()),
            sorted(seq.error_keys()),
            "{name}: error key set @ {threads} threads"
        );
    }
}

// -- SeqProgram cases: cover recv / selective recv / nondet / non-blocking / models -----

#[test]
fn ssr_two_senders_one_receiver() {
    check("s+s+r", Config::default(), || {
        SeqProgram::new(vec![
            vec![send(P2P, 2, "1")],
            vec![send(P2P, 2, "2")],
            vec![recv()],
        ])
    });
}

#[test]
fn ns_nr_three_nonselective() {
    // Three senders to the receiver (tid 3), which reads three times non-selectively: 3!.
    check("ns+nr(3)", Config::default(), || {
        SeqProgram::new(vec![
            vec![send(P2P, 3, "a")],
            vec![send(P2P, 3, "b")],
            vec![send(P2P, 3, "c")],
            vec![recv(), recv(), recv()],
        ])
    });
}

#[test]
fn selective_receives_are_deterministic() {
    // Selective receives fix rf, so exactly one execution - a good check that the parallel
    // merge does not spuriously multiply a single-execution program.
    check("selective", Config::default(), || {
        SeqProgram::new(vec![
            vec![send(P2P, 2, "1")],
            vec![send(P2P, 2, "2")],
            vec![recv_eq("2"), recv_eq("1")],
        ])
    });
}

#[test]
fn nondet_choices() {
    // Two nondet choices plus a receive: exercises the nondet sibling group under forking.
    check("nondet", Config::default(), || {
        SeqProgram::new(vec![
            vec![nondet(&["0", "1", "2"]), send(P2P, 1, "x")],
            vec![nondet(&["0", "1"]), recv()],
        ])
    });
}

#[test]
fn nonblocking_receives_phase_b() {
    // Non-blocking receives may read nothing (multiple at once).
    check("nb-recv", Config::default(), || {
        SeqProgram::new(vec![vec![send(P2P, 1, "x")], vec![recv_nb(), recv_nb()]])
    });
}

#[test]
fn mbox_model() {
    check("mbox", Config::default(), || {
        SeqProgram::new(vec![
            vec![send(Model::Mbox, 2, "1")],
            vec![send(Model::Mbox, 2, "2")],
            vec![recv(), recv()],
        ])
    });
}

// -- System cases: realistic protocols, including error collection ----------------------

#[test]
fn twopc_crash_with_errors() {
    // Crash + monitor + an injected agreement bug => full, blocked and error executions all
    // present, exercising every branch of the report merge.
    let cfg = Config::default().collect_errors();
    check("twopc-crash-bug", cfg, || {
        common::twopc_system(3, P2P, true, true, common::TwoPcBug::DivergentDecision)
    });
}

#[test]
fn leader_crash_with_errors() {
    let cfg = Config::default().collect_errors();
    check("leader-crash-bug", cfg, || {
        common::leader_system(3, 2, P2P, true, true, common::LeaderBug::SelfishTieBreak)
    });
}
