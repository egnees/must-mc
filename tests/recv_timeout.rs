//! Oracles for non-blocking receives (`recv_timeout`), which may time out and read no
//! message (Example 2.5). A mismatch is a bug in the explorer/runtime wiring, never a
//! reason to edit the oracle.
//!
//! ## How non-blocking receives work
//!
//! A non-blocking receive may read "no message" (a timeout) as an **extra** rf source on
//! top of every consistent send. Crucially, "no message" -- unlike a send -- may be read
//! by *several* non-blocking receives at once. This makes `nnr(N)` (N threads each doing
//! one `recv_timeout`, nobody sending) explore exactly **1** execution (all read no
//! message), where the naive nondet encoding `if nondet {recv} else {timeout}` would
//! explore `2^N`.
//!
//! Thread numbering: the paper's `T1/T2/...` are `add`'s 0-based tids `0/1/...`; a
//! `send(k, ...)` targets the 0-based destination tid `k`.

mod common;

use common::{assert_oracle, permutations, recv, recv_nb, sample_perms, send, SeqProgram};
use must::event::Model;
use must::{explore, Config, ExecutionCollector, System};

const P2P: Model = Model::P2p;

// -- nnr(N) = 1 (the headline non-blocking-receive oracle) -------------------------

/// nnr(N): N threads, each one `recv_timeout(any)`; nobody sends. Every receive can only
/// read "no message", so there is exactly **one** consistent execution for any N.
fn nnr(n: usize) -> SeqProgram {
    SeqProgram::new((0..n).map(|_| vec![recv_nb()]).collect())
}

#[test]
fn nnr_2_is_one() {
    // All 2 priority permutations. If "no message" were treated as a single-reader send,
    // "both read no message" would be rejected and the count would collapse below 1.
    assert_oracle("nnr(2)", &nnr(2), &permutations(2), 1, 0);
}

#[test]
fn nnr_3_is_one() {
    assert_oracle("nnr(3)", &nnr(3), &permutations(3), 1, 0);
}

#[test]
fn nnr_5_is_one() {
    // 5 threads: sweep a sample of permutations. Naive encoding would give 2^5 = 32.
    assert_oracle("nnr(5)", &nnr(5), &sample_perms(5), 1, 0);
}

#[test]
fn nnr_8_is_one() {
    // 8 threads: naive would give 2^8 = 256; Must gives exactly 1.
    assert_oracle("nnr(8)", &nnr(8), &sample_perms(8), 1, 0);
}

/// nnr(3) through the **real coroutine runtime** (`ctx.recv_timeout`): still exactly one
/// full execution, proving the runtime -> Program -> explorer path handles no-message
/// reads.
#[test]
fn nnr_3_via_runtime() {
    let build = || {
        let mut sys = System::new();
        for _ in 0..3 {
            sys.add(|c| async move {
                let _ = c.recv_timeout(|_| true).await;
            });
        }
        sys
    };
    for perm in permutations(3) {
        let col = ExecutionCollector::new();
        explore(build, &col, Config::default().with_priorities(perm.clone()));
        assert_eq!(col.full_count(), 1, "runtime nnr(3) under {perm:?}");
        assert_eq!(col.blocked_count(), 0, "runtime nnr(3) under {perm:?}");
    }
}

// -- recv_timeout alongside an available send = 2 ----------------------------------

/// `T0: send(1,"x") || T1: recv_timeout(any)`. T1 may read "x" OR no message -- the
/// timeout branch is explored even though a matching message is available (the timeout
/// may fire first). Exactly 2 full executions.
#[test]
fn recv_timeout_with_available_send_is_two() {
    let prog = SeqProgram::new(vec![vec![send(P2P, 1, "x")], vec![recv_nb()]]);
    assert_oracle("send ∥ recv_timeout", &prog, &permutations(2), 2, 0);
}

/// Same program via the real runtime: 2 full, one reading "x" and one reading no message
/// (surfaced as `None` from `recv_timeout`).
#[test]
fn recv_timeout_with_send_via_runtime() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            c.send(1, "x", Model::P2p);
        });
        sys.add(|c| async move {
            let _ = c.recv_timeout(|_| true).await;
        });
        sys
    };
    let col = ExecutionCollector::new();
    explore(build, &col, Config::default());
    assert_eq!(col.full_count(), 2, "runtime send ∥ recv_timeout");
    assert_eq!(col.blocked_count(), 0);
}

// -- "no message" read by several non-blocking receives at once -------------------

/// `T0: send(1,"x") || T1: recv_timeout(any) || T2: recv_timeout(any)`, send targeting
/// tid 1. T1 may read "x" or no message; T2 has no matching send so it can only read no
/// message. Two full executions: (T1="x", T2=none) and (T1=none, T2=none). The second has
/// "no message" read by *both* receives -- the direct witness that it is not a single-
/// reader send.
fn one_send_two_recv_timeout() -> SeqProgram {
    SeqProgram::new(vec![
        vec![send(P2P, 1, "x")],
        vec![recv_nb()],
        vec![recv_nb()],
    ])
}

#[test]
fn two_recv_timeout_one_send_is_two() {
    assert_oracle(
        "send(1) ∥ recv_timeout ∥ recv_timeout",
        &one_send_two_recv_timeout(),
        &permutations(3),
        2,
        0,
    );
}

/// Largest number of receives reading no message in any collected full execution.
fn max_bottom_readers(col: &ExecutionCollector) -> usize {
    col.full()
        .iter()
        .map(|e| {
            let g = e.graph();
            g.recvs().into_iter().filter(|&r| g.reads_bottom(r)).count()
        })
        .max()
        .unwrap_or(0)
}

/// Direct witness that some full execution has "no message" read by >= 2 receives at
/// once. If it were a single-reader send, that execution would be inconsistent and never
/// appear.
#[test]
fn bottom_is_read_by_multiple_receives() {
    let col = ExecutionCollector::new();
    explore(one_send_two_recv_timeout, &col, Config::default());
    assert_eq!(col.full_count(), 2);
    assert!(
        max_bottom_readers(&col) >= 2,
        "expected a full execution where ⊥ is read by ≥ 2 receives"
    );
}

// -- Mixed blocking + non-blocking receives ----------------------------------------

/// A blocking and a non-blocking receive coexist, both satisfiable:
/// `T0: send(1,"a"); send(2,"b") || T1: recv_timeout(any) || T2: recv(any)`.
/// T2 (blocking, tid 2) must read "b"; T1 (non-blocking, tid 1) may read "a" or no
/// message. Exactly 2 full executions, 0 blocked.
#[test]
fn mixed_blocking_and_nonblocking_full() {
    let prog = SeqProgram::new(vec![
        vec![send(P2P, 1, "a"), send(P2P, 2, "b")],
        vec![recv_nb()],
        vec![recv()],
    ]);
    assert_oracle("mixed full", &prog, &permutations(3), 2, 0);
}

/// The non-blocking receive proceeds while the blocking one blocks:
/// `T0: send(1,"x") || T1: recv_timeout(any) || T2: recv(any)`, send targeting tid 1.
/// T2 (blocking, tid 2) has no matching send, so it always blocks; T1 (non-blocking)
/// finishes reading "x" or no message. Exactly 0 full, 2 blocked -- a maximal consistent
/// prefix in each case, the non-blocking receive resolved and the blocking one stuck
/// (rescheduling).
#[test]
fn mixed_nonblocking_proceeds_while_blocking_blocks() {
    let prog = SeqProgram::new(vec![vec![send(P2P, 1, "x")], vec![recv_nb()], vec![recv()]]);
    assert_oracle("mixed blocked", &prog, &permutations(3), 0, 2);
}
