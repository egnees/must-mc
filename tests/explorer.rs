//! Explorer / backward-revisit tests. Two flavours: table-driven mock programs (no
//! coroutines) that pin the exploration shape, and real `System` programs that exercise
//! the full Program <-> explorer wiring.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};

use must::event::{EventId, Label, Model, Pred};
use must::graph::ExecutionGraph;
use must::observer::Observer;
use must::{
    explore, Config, CountingObserver, ExecutionCollector, Program, System, ThreadNext, Val,
};

// -- Mock program ----------------------------------------------------------------

/// A straight-line, value-independent program: `threads[i]` is thread `i`'s ordered
/// event list. `next` advances by trace length (which equals the number of committed
/// events of the thread), so it needs no coroutine replay. Adequate for s+s+r and
/// s+s+r-br, whose control flow does not branch on received values.
#[derive(Clone)]
struct SeqProgram {
    threads: Vec<Vec<Label>>,
}

impl Program for SeqProgram {
    fn num_threads(&self) -> usize {
        self.threads.len()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        self.threads
            .iter()
            .enumerate()
            .map(|(i, evs)| {
                let done = traces[i].len();
                if done < evs.len() {
                    ThreadNext::Next(evs[done].clone())
                } else {
                    ThreadNext::Finished
                }
            })
            .collect()
    }
}

fn send(dst: usize, v: &str) -> Label {
    Label::send(Model::P2p, dst, v)
}
fn recv() -> Label {
    Label::recv(Pred::any())
}

/// s+s+r: `T0: send(2,1) || T1: send(2,2) || T2: recv()`.
fn ssr_mock() -> SeqProgram {
    SeqProgram {
        threads: vec![vec![send(2, "1")], vec![send(2, "2")], vec![recv()]],
    }
}

/// s+s+r-br (Example 4.3): `T0: send(0,0); recv() || T1: send(3,1) || T2: send(3,2) ||
/// T3: recv() || T4: send(0,42)`.
fn ssr_br_mock() -> SeqProgram {
    SeqProgram {
        threads: vec![
            vec![send(0, "0"), recv()], // T0 sends to itself, then receives
            vec![send(3, "1")],
            vec![send(3, "2")],
            vec![recv()],
            vec![send(0, "42")],
        ],
    }
}

/// ns+r(3): `T0..T2: send(3,i) || T3: recv()`. Exactly 3 full executions (the receive
/// reads one of the three sends). It exercises the "union {r}" clause of Algorithm 1
/// line 12: under priorities [0,1,3,2] the second/third sends backward-revisit the
/// already-added receive, and only checking `RevisitCondition` on `r` itself keeps the
/// count at 3 instead of 4.
fn nsr3_mock() -> SeqProgram {
    SeqProgram {
        threads: vec![
            vec![send(3, "1")],
            vec![send(3, "2")],
            vec![send(3, "3")],
            vec![recv()],
        ],
    }
}

/// A1: `T0: recv() || T1: send(0,a); send(0,b) || T2: send(0,c)`, all under `model`.
/// Under asyn the receive may read any of a/b/c (3 full); under p2p reading `b` while
/// the earlier same-sender `a` is unread is inconsistent, so 2 full (a or c). T1's two
/// sends are porf-connected (a ->po b), so this catches a wrongly-forbidden repeated
/// revisit of one receive and a miscomputed `Previous`.
fn a1_mock(model: Model) -> SeqProgram {
    SeqProgram {
        threads: vec![
            vec![recv()],
            vec![Label::send(model, 0, "a"), Label::send(model, 0, "b")],
            vec![Label::send(model, 0, "c")],
        ],
    }
}

// -- Helpers ---------------------------------------------------------------------

/// Every permutation of `0..n` (n small).
fn permutations(n: usize) -> Vec<Vec<usize>> {
    fn go(cur: &mut Vec<usize>, rest: &BTreeSet<usize>, out: &mut Vec<Vec<usize>>) {
        if rest.is_empty() {
            out.push(cur.clone());
            return;
        }
        for &x in rest {
            let mut r2 = rest.clone();
            r2.remove(&x);
            cur.push(x);
            go(cur, &r2, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    go(&mut Vec::new(), &(0..n).collect(), &mut out);
    out
}

/// No two terminal (full or blocked) executions share a canonical key (Theorem 4.1).
fn assert_no_duplicates(col: &ExecutionCollector) {
    let keys = col.terminal_keys();
    let unique: BTreeSet<&String> = keys.iter().collect();
    assert_eq!(
        keys.len(),
        unique.len(),
        "duplicate canonical keys among terminal executions:\n{keys:#?}"
    );
}

fn run<P: Program>(make: impl Fn() -> P + Sync, priorities: Vec<usize>) -> ExecutionCollector {
    let col = ExecutionCollector::new();
    explore(make, &col, Config::default().with_priorities(priorities));
    col
}

// -- s+s+r: 2 executions under every priority permutation ------------------------

#[test]
fn ssr_two_executions_all_permutations() {
    let prog = ssr_mock();
    for perm in permutations(3) {
        let col = run(|| prog.clone(), perm.clone());
        assert_eq!(
            col.full_count(),
            2,
            "s+s+r under priorities {perm:?} should give 2 full executions"
        );
        assert_eq!(col.blocked_count(), 0, "s+s+r has no blocked executions");
        assert_eq!(col.error_count(), 0);
        assert_no_duplicates(&col);
    }
}

/// Rescheduling (Example 4.1): the receiver (T2) is highest priority but has no message
/// initially -- the run still yields 2 executions.
#[test]
fn ssr_rescheduling_receiver_first() {
    let col = run(ssr_mock, vec![2, 0, 1]);
    assert_eq!(col.full_count(), 2);
    assert_eq!(col.blocked_count(), 0);
    assert_no_duplicates(&col);
}

/// Backward revisit (Example 4.2): T0 and T2 scheduled before T1, so the receive is
/// added while only one send exists and the second send backward-revisits it.
#[test]
fn ssr_backward_revisit_path() {
    let obs = (ExecutionCollector::new(), CountingObserver::new());
    explore(
        ssr_mock,
        &obs,
        Config::default().with_priorities(vec![0, 2, 1]),
    );
    assert_eq!(obs.0.full_count(), 2);
    assert_no_duplicates(&obs.0);
    // Exactly one backward revisit happens on this schedule (the second send revisits
    // the already-added receive).
    assert_eq!(obs.1.backward_revisits(), 1);
}

// -- s+s+r-br (Example 4.3): 4 executions, revisit only from graph B ---------------

#[test]
fn ssr_br_four_executions_all_permutations() {
    let prog = ssr_br_mock();
    for perm in permutations(5) {
        let col = run(|| prog.clone(), perm.clone());
        assert_eq!(
            col.full_count(),
            4,
            "s+s+r-br under priorities {perm:?} should give 4 full executions"
        );
        assert_eq!(col.blocked_count(), 0, "s+s+r-br has no blocked executions");
        assert_eq!(col.error_count(), 0);
        assert_no_duplicates(&col);
    }
}

// -- ns+r(3): the "union {r}" clause of Algorithm 1 line 12 -----------------------

#[test]
fn nsr3_three_executions_all_permutations() {
    let prog = nsr3_mock();
    for perm in permutations(4) {
        let col = run(|| prog.clone(), perm.clone());
        assert_eq!(
            col.full_count(),
            3,
            "ns+r(3) under priorities {perm:?} should give exactly 3 full executions"
        );
        assert_eq!(col.blocked_count(), 0);
        assert_eq!(col.error_count(), 0);
        assert_no_duplicates(&col);
    }
}

/// A schedule that yields 4 without the `chain(once(&r))` guard.
#[test]
fn nsr3_regression_priorities_0_1_3_2() {
    let col = run(nsr3_mock, vec![0, 1, 3, 2]);
    assert_eq!(col.full_count(), 3);
    assert_no_duplicates(&col);
}

// -- A1: repeated revisit of one receive from porf-connected sends ----------------

#[test]
fn a1_asyn_three_executions_all_permutations() {
    let prog = a1_mock(Model::Asyn);
    for perm in permutations(3) {
        let col = run(|| prog.clone(), perm.clone());
        assert_eq!(
            col.full_count(),
            3,
            "A1 (asyn) under priorities {perm:?} should give 3 full executions"
        );
        assert_eq!(col.blocked_count(), 0);
        assert_no_duplicates(&col);
    }
}

#[test]
fn a1_p2p_two_executions_all_permutations() {
    let prog = a1_mock(Model::P2p);
    for perm in permutations(3) {
        let col = run(|| prog.clone(), perm.clone());
        assert_eq!(
            col.full_count(),
            2,
            "A1 (p2p) under priorities {perm:?} should give 2 full executions (a or c)"
        );
        assert_eq!(col.blocked_count(), 0);
        assert_no_duplicates(&col);
    }
}

/// Counts backward revisits of a receive in thread 0 by a send in thread 4 --
/// i.e. `R(T0) <- S(T4,42)` in Example 4.3.
#[derive(Default)]
struct T0FromT4Spy {
    count: AtomicUsize,
}
impl T0FromT4Spy {
    fn count(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }
}
impl Observer for T0FromT4Spy {
    fn on_backward_revisit(
        &self,
        _g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        _deleted: &BTreeSet<EventId>,
    ) {
        if r.tid == 0 && s.tid == 4 {
            self.count.fetch_add(1, Ordering::Relaxed);
        }
    }
}

/// At the default LTR priorities, `R(T0) <- S(T4,42)` is performed exactly once (from
/// the canonical graph B, not from C) -- the whole point of the revisiting condition.
#[test]
fn ssr_br_revisit_r_t0_from_s_t4_is_unique() {
    let obs = (ExecutionCollector::new(), T0FromT4Spy::default());
    explore(ssr_br_mock, &obs, Config::default());
    assert_eq!(obs.0.full_count(), 4);
    assert_eq!(
        obs.1.count(),
        1,
        "R(T0)←S(T4,42) must be revisited exactly once (only from graph B)"
    );
    assert_no_duplicates(&obs.0);
}

// -- Runtime System wiring --------------------------------------------------------

/// s+s+r built from three real coroutine processes -- checks Program <-> explorer through
/// the actual runtime, not a mock.
#[test]
fn ssr_via_runtime_system() {
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
        let col = run(build, perm.clone());
        assert_eq!(col.full_count(), 2, "runtime s+s+r under {perm:?}");
        assert_no_duplicates(&col);
    }
}

/// A send in parallel with a receive whose predicate never matches: 0 full, 1 blocked.
/// Also checks that the predicate participates in addability.
#[test]
fn blocked_execution_via_runtime() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            c.send(1, "a", Model::P2p);
        });
        sys.add(|c| async move {
            // waits for "b", which is never sent
            let _ = c.recv(|x| x == "b").await;
        });
        sys
    };

    let obs = (ExecutionCollector::new(), CountingObserver::new());
    explore(build, &obs, Config::default());
    assert_eq!(
        obs.0.full_count(),
        0,
        "no full execution: recv never matches"
    );
    assert_eq!(obs.0.blocked_count(), 1, "exactly one blocked execution");
    assert!(obs.1.threads_blocked() >= 1);
    assert_no_duplicates(&obs.0);
}

/// Out-of-order selective receives (Example 2.8): one p2p-consistent graph.
#[test]
fn selective_out_of_order_receive() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            c.send(1, "1", Model::P2p);
            c.send(1, "2", Model::P2p);
        });
        sys.add(|c| async move {
            let _ = c.recv(|x| x == "2").await;
            let _ = c.recv(|x| x == "1").await;
        });
        sys
    };

    let col = run(build, vec![0, 1]);
    assert_eq!(col.full_count(), 1, "exactly one p2p graph (crossed rf)");
    assert_no_duplicates(&col);
}

// -- An execution's public surface ------------------------------------------------

#[test]
fn executions_expose_pending_sends() {
    // Two sends to a receiver that reads one: the other stays pending.
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

    let col = run(build, vec![0, 1, 2]);
    assert_eq!(col.full_count(), 2);
    // Every full execution has exactly one unread send left over.
    let pending_counts: BTreeMap<usize, usize> = col
        .full()
        .iter()
        .map(|e| e.pending_sends().len())
        .fold(BTreeMap::new(), |mut m, c| {
            *m.entry(c).or_insert(0) += 1;
            m
        });
    assert_eq!(
        pending_counts.get(&1),
        Some(&2),
        "each full exec leaves 1 pending send"
    );
}

// -- collect_errors: an error finishes only its own thread ------------------------

/// `T0: recv(); assert(v == "c") || T1: send(0,a) || T2: send(0,b)`. Both rf choices make
/// T0's assert fail, so both branches are erroneous.
fn two_error_prog() -> System {
    let mut sys = System::new();
    sys.add(|c| async move {
        let v = c.recv(|_| true).await;
        c.assert_that(v == "c", "want c");
    });
    sys.add(|c| async move {
        c.send(0, "a", Model::P2p);
    });
    sys.add(|c| async move {
        c.send(0, "b", Model::P2p);
    });
    sys
}

/// collect_errors keeps exploring, so it finds *both* erroneous executions; the default
/// (stop-on-error) reports just the first and halts.
#[test]
fn collect_errors_finds_all_reachable_errors() {
    let collected = ExecutionCollector::new();
    explore(
        two_error_prog,
        &collected,
        Config::default().collect_errors(),
    );
    assert_eq!(collected.error_count(), 2, "both rf choices reach an error");
    assert_eq!(collected.full_count(), 0);
    // No two erroneous executions coincide.
    let keys: BTreeSet<String> = collected.error_keys().into_iter().collect();
    assert_eq!(keys.len(), 2, "the two error executions are distinct");

    let default = ExecutionCollector::new();
    explore(two_error_prog, &default, Config::default());
    assert_eq!(default.error_count(), 1, "default stops at the first error");
    assert_eq!(default.full_count(), 0);
}

/// A tricky case: `T0: assert(false) || T1: recv(); assert(v=="x") || T2: send(1,"x")`.
/// A "truncate the whole branch" behaviour would never explore T1 after T0 errored; the
/// honest version runs T1/T2 to completion, so the recorded error graph contains T1's
/// receive -- proof the branch continued.
#[test]
fn collect_errors_continues_past_an_error() {
    let build = || {
        let mut sys = System::new();
        sys.add(|c| async move {
            c.assert_that(false, "boom");
        });
        sys.add(|c| async move {
            let v = c.recv(|_| true).await;
            c.assert_that(v == "x", "want x");
        });
        sys.add(|c| async move {
            c.send(1, "x", Model::P2p);
        });
        sys
    };

    let col = ExecutionCollector::new();
    explore(build, &col, Config::default().collect_errors());
    assert!(col.error_count() >= 1, "T0's error is reported");
    // Some erroneous execution ran thread 1 (its receive) after T0's error -- impossible
    // if the branch had been truncated at T0.
    let t1_explored = col.errors().iter().any(|e| e.graph().thread_len(1) >= 1);
    assert!(t1_explored, "thread 1 was explored after T0's error");
}

/// collect_errors must not change error-free counts: s+s+r is still 2, ns+r(3) still 3.
#[test]
fn collect_errors_preserves_error_free_counts() {
    let ssr = ssr_mock();
    for perm in permutations(3) {
        let col = ExecutionCollector::new();
        explore(
            || ssr.clone(),
            &col,
            Config::default()
                .with_priorities(perm.clone())
                .collect_errors(),
        );
        assert_eq!(col.full_count(), 2, "s+s+r collect_errors under {perm:?}");
        assert_eq!(col.error_count(), 0);
        assert_no_duplicates(&col);
    }
    let col = ExecutionCollector::new();
    explore(nsr3_mock, &col, Config::default().collect_errors());
    assert_eq!(col.full_count(), 3);
    assert_eq!(col.error_count(), 0);
}
