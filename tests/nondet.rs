//! Data-nondeterminism oracles (`ND^S` events, Algorithm 1 lines 6 & 19). A mismatch is a
//! bug in the explorer/runtime wiring, never a reason to edit the oracle.
//!
//! ## How data non-determinism works
//!
//! A nondet event `ND^S` enumerates *every* value of its finite option set `S` (line 6),
//! each choice recursing through plain `Visit_P` (assigning a nondet value never changes
//! consistency). Two executions that differ only in a nondet value are different graphs,
//! so the chosen value is part of the canonical key. In a backward revisit the nondet
//! event is canonical iff it chose `min(S)` (line 19), which -- like every canonical-
//! source rule -- is what keeps a revisit firing from a single graph.
//!
//! Thread numbering: the paper's `T1/T2/...` are `add`'s 0-based tids `0/1/...`; a
//! `send(k, ...)` targets the 0-based destination tid `k`.

mod common;

use std::collections::BTreeSet;

use common::{assert_oracle, nondet, permutations, recv, send, SeqProgram};
use must::event::Model;
use must::{explore, Config, ExecutionCollector, System};

const P2P: Model = Model::P2p;

// -- 1. A single nondet enumerates its whole option set -----------------------------

/// `T0: nondet(["0","1","2"])` alone -> one full execution per value = 3, none blocked.
#[test]
fn single_nondet_enumerates_all_values() {
    let prog = SeqProgram::new(vec![vec![nondet(&["0", "1", "2"])]]);
    assert_oracle("nondet(3)", &prog, &permutations(1), 3, 0);
}

// -- 2. Independent nondets multiply -------------------------------------------------

/// Two independent 2-value nondets in two threads -> 2*2 = 4 full executions, and the
/// terminal set is priority-invariant (the choices are concurrent).
#[test]
fn two_independent_nondets_are_four() {
    let prog = SeqProgram::new(vec![vec![nondet(&["0", "1"])], vec![nondet(&["0", "1"])]]);
    assert_oracle("nondet ∥ nondet", &prog, &permutations(2), 4, 0);
}

/// Three independent 2-value nondets in three threads -> 2^3 = 8 full executions.
#[test]
fn three_independent_nondets_are_eight() {
    let prog = SeqProgram::new(vec![
        vec![nondet(&["0", "1"])],
        vec![nondet(&["0", "1"])],
        vec![nondet(&["0", "1"])],
    ]);
    assert_oracle("nondet³", &prog, &permutations(3), 8, 0);
}

// -- Runtime helpers ----------------------------------------------------------------

/// Run `sys` under every priority permutation of `n` threads; assert no duplicate
/// terminals and a priority-invariant terminal-key set, and return `(full, blocked)`.
fn run_system_perms(make: impl Fn() -> System + Sync, n: usize, name: &str) -> (usize, usize) {
    let mut reference: Option<BTreeSet<String>> = None;
    let mut counts = (0, 0);
    for perm in permutations(n) {
        let col = ExecutionCollector::new();
        explore(&make, &col, Config::default().with_priorities(perm.clone()));
        let keys = col.terminal_keys();
        let set: BTreeSet<String> = keys.iter().cloned().collect();
        assert_eq!(
            keys.len(),
            set.len(),
            "{name}: duplicate terminal keys under priorities {perm:?}:\n{keys:#?}"
        );
        match &reference {
            None => {
                reference = Some(set);
                counts = (col.full_count(), col.blocked_count());
            }
            Some(r) => assert_eq!(
                &set, r,
                "{name}: terminal key set differs under priorities {perm:?}"
            ),
        }
    }
    counts
}

/// The multiset of values every receive read across all collected full executions.
fn read_values(col: &ExecutionCollector) -> BTreeSet<String> {
    let mut vals = BTreeSet::new();
    for e in col.full() {
        let g = e.graph();
        for r in g.recvs() {
            if let Some(s) = g.reads_from(r) {
                if let Some(v) = g.label(s).val() {
                    vals.insert(v.to_string());
                }
            }
        }
    }
    vals
}

// -- 3. Nondet through the real runtime ---------------------------------------------

/// `T0: let v = nondet(["1","2"]).await; send(1, v) || T1: recv()`. The nondet feeds the
/// send payload, so the receive reads "1" or "2": exactly 2 full executions.
#[test]
fn nondet_feeds_send_value_via_runtime() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            let v = c.nondet(["1", "2"]).await;
            c.send(1, v, Model::P2p);
        });
        sys.add(|c| async move {
            let _ = c.recv(|_| true).await;
        });
        sys
    };
    let (full, blocked) = run_system_perms(build, 2, "nondet→send");
    assert_eq!((full, blocked), (2, 0));

    let col = ExecutionCollector::new();
    explore(build, &col, Config::default());
    assert_eq!(
        read_values(&col),
        ["1", "2"].iter().map(|s| s.to_string()).collect(),
        "the receive should read each nondet-chosen send value"
    );
}

/// Control flow branches on a nondet: `T0: if nondet(["0","1"]) == "0" { send(1,"a") }
/// else { send(1,"b") } || T1: recv()`. Two full executions where the receive reads "a"
/// (nondet "0") or "b" (nondet "1").
#[test]
fn nondet_controls_branch_via_runtime() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            if c.nondet(["0", "1"]).await == "0" {
                c.send(1, "a", Model::P2p);
            } else {
                c.send(1, "b", Model::P2p);
            }
        });
        sys.add(|c| async move {
            let _ = c.recv(|_| true).await;
        });
        sys
    };
    let (full, blocked) = run_system_perms(build, 2, "nondet→branch");
    assert_eq!((full, blocked), (2, 0));

    let col = ExecutionCollector::new();
    explore(build, &col, Config::default());
    assert_eq!(
        read_values(&col),
        ["a", "b"].iter().map(|s| s.to_string()).collect(),
        "the receive should read the branch's send value"
    );
}

// -- 4. Nondet combined with backward revisit ---------------------------------------

/// `T0: let v = nondet(["1","2"]).await; send(2, v) || T1: send(2,"9") || T2: recv()`.
/// The receive reads T0's send or T1's send, independently of T0's nondet choice, so
/// there are 2 rf-choices * 2 nondet values = 4 full executions. Crucially the two
/// executions where the receive reads T1's "9" have identical events and rf and differ
/// *only* in the nondet value -- they stay distinct because the value is part of the
/// canonical key. No duplicates, priority-invariant.
#[test]
fn nondet_times_backward_revisit_is_four() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            let v = c.nondet(["1", "2"]).await;
            c.send(2, v, Model::P2p);
        });
        sys.add(|c| async move {
            c.send(2, "9", Model::P2p);
        });
        sys.add(|c| async move {
            let _ = c.recv(|_| true).await;
        });
        sys
    };
    let (full, blocked) = run_system_perms(build, 3, "nondet × backward revisit");
    assert_eq!((full, blocked), (4, 0));
}

/// A nondet event that lands in a revisit's `Deleted` set -- the direct witness for line
/// 19's *rejection* path. `T0: recv() || T1: nondet(["0","1"]) || T2: send(0,"x") || T3:
/// send(0,"y")`. Under an order that adds T0's receive (reading one send) and T1's nondet
/// before the other send, that send backward-revisits the receive; the nondet is deleted
/// (it is added after the receive and is not in the send's porf-prefix), so the revisit
/// fires only from the canonical graph where the nondet chose min(S) = "0" (line 19).
/// Were line 19 wrong, the revisit would fire from both nondet graphs, re-adding the
/// nondet twice and duplicating the (recv<-other, nondet=*) executions. The receive reads
/// "x" or "y" and the nondet is "0" or "1" independently: exactly 4 full, no duplicates,
/// priority-invariant.
#[test]
fn nondet_in_deleted_set_is_gated_by_line19() {
    let prog = SeqProgram::new(vec![
        vec![recv()],
        vec![nondet(&["0", "1"])],
        vec![send(P2P, 0, "x")],
        vec![send(P2P, 0, "y")],
    ]);
    assert_oracle("nondet in Deleted", &prog, &permutations(4), 4, 0);
}
