//! Execution-count oracles under p2p (the paper, Table 1). A mismatch is a bug in the
//! explorer, never a reason to edit the oracle.
//!
//! ## Provenance of the numbers
//!
//! * **From the paper directly** (Table 1, or the examples it is built on): s+s+r = 2,
//!   Example 2.8 = 1, ns+r(2/5/8) = 2/5/8, ns+nr(2/5/8) = 2/120/40320,
//!   ns+nr-sel(2/5/8) = 1, nworkers(7) = 10080.
//! * **Formula / interpolation, anchored on a paper number** (flagged at each use):
//!   ns+nr(4) = 24 interpolates the `N!` law; nworkers(3/4/6) = 2*N! extends the sanity
//!   identity `nworkers(N) = 2*N!`, whose N=7 value 10080 *is* in Table 1.
//! * **Not in the paper** -- the s+s+r-br (Example 4.3) oracle = 4 (derived by hand from
//!   Algorithm 1) lives in `tests/explorer.rs`, not here.
//!
//! Thread numbering: the paper's `T1/T2/T3` are `System.add`'s 0-based tids `0/1/2`.
//! Where a program targets "the receiver" it is the *last* thread; a `send(k, ...)` below
//! is already the 0-based destination tid. (Example 2.8 keeps the paper's T-numbering --
//! see its comment.)

mod common;

use std::collections::BTreeMap;

use common::{
    assert_no_duplicates, assert_oracle, assert_oracle_default, factorial, permutations, recv,
    recv_eq, sample_perms, send, SeqProgram,
};
use must::event::Model;
use must::{explore, Config, ExecutionCollector, System};

const P2P: Model = Model::P2p;

// -- Program builders -------------------------------------------------------------

/// s+s+r: `T0: send(2,1) || T1: send(2,2) || T2: recv()` -- two senders to the receiver
/// (tid 2). The receive reads one of the two sends: 2 full executions.
fn ssr() -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(P2P, 2, "1")],
        vec![send(P2P, 2, "2")],
        vec![recv()],
    ])
}

/// ns+r(N): `T0..T(N-1): send(N, i) || TN: recv()`. N senders to the receiver (tid N),
/// one blocking receive that reads exactly one of them: N full executions (lazy
/// ordering -- N instead of N!).
fn ns_r(n: usize) -> SeqProgram {
    let mut threads: Vec<_> = (0..n).map(|i| vec![send(P2P, n, &i.to_string())]).collect();
    threads.push(vec![recv()]);
    SeqProgram::new(threads)
}

/// ns+nr(N): `T0..T(N-1): send(N, i) || TN: recv() ... recv()` (N receives). N sends
/// consumed by N non-selective receives in one thread: every permutation of the
/// delivery order is a distinct execution -- N! full executions.
fn ns_nr(n: usize) -> SeqProgram {
    let mut threads: Vec<_> = (0..n).map(|i| vec![send(P2P, n, &i.to_string())]).collect();
    threads.push((0..n).map(|_| recv()).collect());
    SeqProgram::new(threads)
}

/// ns+nr-sel(N): like ns+nr but the k-th receive is selective (`recv(x == k)`). Each
/// receive matches exactly one send, so there is a single consistent execution for any
/// N (selective receives collapse the N! down to 1).
fn ns_nr_sel(n: usize) -> SeqProgram {
    let mut threads: Vec<_> = (0..n).map(|i| vec![send(P2P, n, &i.to_string())]).collect();
    threads.push((0..n).map(|i| recv_eq(&i.to_string())).collect());
    SeqProgram::new(threads)
}

/// nworkers(N): main (tid 0) sends a message to *itself*, then receives; N workers
/// (tids 1..=N) each send to the coordinator (tid N+1); the coordinator receives all N
/// then sends "done" to main. The coordinator's N receives can consume the workers in
/// any order (N! ways) and main's receive may read either its own message or the
/// coordinator's (2 ways): 2*N! full executions (note the send-to-self).
fn nworkers(n: usize) -> SeqProgram {
    let coord = n + 1;
    let mut threads = vec![vec![send(P2P, 0, "self"), recv()]]; // main
    for w in 0..n {
        threads.push(vec![send(P2P, coord, &format!("w{w}"))]);
    }
    let mut coord_evs: Vec<_> = (0..n).map(|_| recv()).collect();
    coord_evs.push(send(P2P, 0, "done"));
    threads.push(coord_evs);
    SeqProgram::new(threads)
}

// -- s+s+r ------------------------------------------------------------------------

#[test]
fn ssr_two_full_all_permutations() {
    // All 6 priority permutations, incl. receiver-first (rescheduling) and
    // sender+receiver-first (backward revisit).
    assert_oracle("s+s+r", &ssr(), &permutations(3), 2, 0);
}

// -- ns+r(N) = N ------------------------------------------------------------------

#[test]
fn nsr_2() {
    assert_oracle("ns+r(2)", &ns_r(2), &permutations(3), 2, 0);
}

#[test]
fn nsr_5() {
    // 6 threads: sweep a sample of permutations rather than all 720.
    assert_oracle("ns+r(5)", &ns_r(5), &sample_perms(6), 5, 0);
}

#[test]
fn nsr_8() {
    // 9 threads: default + reverse + rotation. 8 executions, trivially cheap.
    assert_oracle("ns+r(8)", &ns_r(8), &sample_perms(9), 8, 0);
}

// -- ns+nr(N) = N! ----------------------------------------------------------------

#[test]
fn nsnr_2() {
    assert_oracle("ns+nr(2)", &ns_nr(2), &permutations(3), factorial(2), 0);
}

#[test]
fn nsnr_4() {
    // 24 = 4! interpolates the N! law (Table 1 tabulates only N = 2/5/8). 5 threads =
    // 120 permutations; each yields 24 executions.
    assert_oracle("ns+nr(4)", &ns_nr(4), &permutations(5), factorial(4), 0);
}

#[test]
fn nsnr_5() {
    assert_oracle("ns+nr(5)", &ns_nr(5), &sample_perms(6), factorial(5), 0);
}

/// N=8 gives 40320 executions. Heavy, so it runs only in release builds
/// (`cargo test --release`).
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: 40320 executions; run with --release"
)]
fn nsnr_8() {
    assert_oracle_default("ns+nr(8)", &ns_nr(8), factorial(8), 0);
}

// -- ns+nr-sel(N) = 1 -------------------------------------------------------------

#[test]
fn nsnr_sel_2() {
    assert_oracle("ns+nr-sel(2)", &ns_nr_sel(2), &permutations(3), 1, 0);
}

#[test]
fn nsnr_sel_5() {
    assert_oracle("ns+nr-sel(5)", &ns_nr_sel(5), &sample_perms(6), 1, 0);
}

#[test]
fn nsnr_sel_8() {
    assert_oracle("ns+nr-sel(8)", &ns_nr_sel(8), &sample_perms(9), 1, 0);
}

// -- Example 2.8: crossed selective receives = 1 ----------------------------------

/// `T1: send(T2,1); send(T2,2) || T2: recv(x==2); recv(x==1)`. Here the paper's
/// T-numbering is kept: `send(T2, ...)` targets tid 1 (the second, receiving thread).
/// Under p2p the two same-sender messages arrive in send order, so the only consistent
/// reading is the crossed one (2nd receive gets "1"): exactly 1 execution.
#[test]
fn example_2_8_one_full() {
    let prog = SeqProgram::new(vec![
        vec![send(P2P, 1, "1"), send(P2P, 1, "2")],
        vec![recv_eq("2"), recv_eq("1")],
    ]);
    assert_oracle("Example 2.8", &prog, &permutations(2), 1, 0);
}

// -- nworkers(N) = 2*N! -----------------------------------------------------------

#[test]
fn nworkers_3() {
    // 12 = 2*3! by the 2*N! identity (Table 1 tabulates only N >= 7). 5
    // threads; all 120 permutations, 12 executions each.
    assert_oracle(
        "nworkers(3)",
        &nworkers(3),
        &permutations(5),
        2 * factorial(3),
        0,
    );
}

#[test]
fn nworkers_4() {
    // 48 = 2*4! (formula). 6 threads; sample of permutations.
    assert_oracle(
        "nworkers(4)",
        &nworkers(4),
        &sample_perms(6),
        2 * factorial(4),
        0,
    );
}

/// nworkers(6) = 1440 = 2*6! (formula). Heavy, so it runs only in release builds.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: 1440 executions; run with --release"
)]
fn nworkers_6() {
    assert_oracle_default("nworkers(6)", &nworkers(6), 2 * factorial(6), 0);
}

/// nworkers(7) = 10080, the value reported in the paper. Heavy, so it runs only in
/// release builds.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "heavy: 10080 executions; run with --release"
)]
fn nworkers_7() {
    assert_oracle_default("nworkers(7)", &nworkers(7), 2 * factorial(7), 0);
}

// -- blocked executions (maximal consistent prefixes) -----------------------------

/// Degenerate blocked oracle: `T0: send(1,"a") || T1: recv(x=="b")`. The predicate never
/// matches the only send, so there is no full execution and exactly one blocked one (the
/// receive is never added). Also checks the predicate participates in addability.
#[test]
fn blocked_no_matching_message() {
    let prog = SeqProgram::new(vec![vec![send(P2P, 1, "a")], vec![recv_eq("b")]]);
    assert_oracle("blocked (no match)", &prog, &permutations(2), 0, 1);
}

/// Non-degenerate blocked oracle -- a program with both a full *and* a blocked terminal:
/// `T0: recv(); recv(x=="b") || T1: send(0,"a") || T2: send(0,"b")`. T0's first (any)
/// receive reads "a" or "b"; the second (`x=="b"`) needs "b".
///   * If the first reads "a", the second reads "b" -- a full execution.
///   * If the first reads "b", "b" is consumed, so the second `recv(x=="b")` has no
///     matching unread send and T0 blocks there -- a maximal consistent prefix.
///
/// So exactly 1 full + 1 blocked under every permutation. This exercises the blocked
/// classification on a non-trivial graph (the degenerate oracle above has no full path),
/// mirroring the fuzz harness's full-and-blocked terminal check.
#[test]
fn blocked_and_full_coexist() {
    let prog = SeqProgram::new(vec![
        vec![recv(), recv_eq("b")],
        vec![send(P2P, 0, "a")],
        vec![send(P2P, 0, "b")],
    ]);
    assert_oracle("blocked+full", &prog, &permutations(3), 1, 1);
}

// -- Runtime cross-checks: the same numbers through the real System runtime ---------

/// s+s+r built from three coroutine processes -- 2 full under every permutation, proving
/// the runtime -> Program -> explorer path agrees with the mock.
#[test]
fn ssr_via_runtime() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            c.send(2, "1", Model::P2p);
        });
        sys.add(|c| async move {
            c.send(2, "2", Model::P2p);
        });
        sys.add(|c| async move {
            let _ = c.recv(|_| true).await;
        });
        sys
    };
    for perm in permutations(3) {
        let col = ExecutionCollector::new();
        explore(build, &col, Config::default().with_priorities(perm.clone()));
        assert_eq!(col.full_count(), 2, "runtime s+s+r under {perm:?}");
        assert_no_duplicates(&col, "runtime s+s+r");
    }
}

/// ns+nr-sel(3) through the real runtime with genuine selective-receive closures -- one
/// execution, confirming selectivity is honoured by the runtime path (not just the mock).
#[test]
fn nsnr_sel_via_runtime() {
    let build = || {
        let mut sys = System::new();
        for i in 0..3u32 {
            sys.add(move |c| async move {
                c.send(3, i.to_string(), Model::P2p);
            });
        }
        sys.add(|c| async move {
            for i in 0..3u32 {
                let want = i.to_string();
                let _ = c.recv(move |x: &str| want == x).await;
            }
        });
        sys
    };
    let col = ExecutionCollector::new();
    explore(build, &col, Config::default());
    assert_eq!(col.full_count(), 1, "runtime ns+nr-sel(3)");
    assert_eq!(col.blocked_count(), 0);
    assert_no_duplicates(&col, "runtime ns+nr-sel(3)");
}

/// nworkers(3) through the real runtime, exercising send-to-self: 2*3! = 12 executions.
#[test]
fn nworkers_via_runtime() {
    let build = || {
        let mut sys = System::new();
        // main = tid 0: send to self, then receive (own message OR coordinator's).
        sys.add(|c| async move {
            c.send(0, "self", Model::P2p);
            let _ = c.recv(|_| true).await;
        });
        // workers = tids 1..=3: send to coordinator (tid 4).
        for w in 0..3u32 {
            sys.add(move |c| async move {
                c.send(4, format!("w{w}"), Model::P2p);
            });
        }
        // coordinator = tid 4: receive all 3, then send to main.
        sys.add(|c| async move {
            for _ in 0..3 {
                let _ = c.recv(|_| true).await;
            }
            c.send(0, "done", Model::P2p);
        });
        sys
    };

    let col = ExecutionCollector::new();
    explore(build, &col, Config::default());
    assert_eq!(col.full_count(), 12, "runtime nworkers(3) = 2·3!");
    assert_eq!(col.blocked_count(), 0);
    assert_no_duplicates(&col, "runtime nworkers(3)");
}

// -- pending sends surface (the seam for the time-interval extension) --------------

/// Every ns+r-style full execution leaves exactly the sends the receive did not read as
/// pending -- the seam the time-interval extension reasons over.
#[test]
fn pending_sends_are_the_unread_sends() {
    let col = ExecutionCollector::new();
    explore(|| ns_r(3), &col, Config::default());
    assert_eq!(col.full_count(), 3);
    let pending: BTreeMap<usize, usize> =
        col.full()
            .iter()
            .map(|e| e.pending_sends().len())
            .fold(BTreeMap::new(), |mut m, c| {
                *m.entry(c).or_insert(0) += 1;
                m
            });
    // 3 sends, 1 read: each full execution leaves 2 pending.
    assert_eq!(
        pending.get(&2),
        Some(&3),
        "each full exec leaves 2 pending sends"
    );
}
