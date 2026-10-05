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
            vec![send(0, "0"), recv()],
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

#[test]
fn forward_dfs_restores_every_parent_including_stopping_paths() {
    #[derive(Default)]
    struct ParentSnapshots {
        stack: std::sync::Mutex<Vec<ExecutionGraph>>,
        visits: AtomicUsize,
    }
    impl Observer for ParentSnapshots {
        fn on_visit_enter(&self, g: &ExecutionGraph) {
            self.stack.lock().unwrap().push(g.clone());
            self.visits.fetch_add(1, Ordering::Relaxed);
        }
        fn on_visit_exit(&self, g: &ExecutionGraph, _productive: bool) {
            let parent = self.stack.lock().unwrap().pop().unwrap();
            assert_eq!(g.canonical_key(), parent.canonical_key());
            assert_eq!(g.num_threads(), parent.num_threads());
            assert_eq!(g.num_sends(), parent.num_sends());
            for e in parent.iter_events() {
                assert_eq!(g.stamp(e), parent.stamp(e));
            }
        }
    }
    let program = SeqProgram {
        threads: vec![
            vec![send(2, "a"), send(2, "b")],
            vec![send(2, "c"), Label::nondet(["x", "y"])],
            vec![
                Label::recv_nb(Pred::any()),
                recv(),
                Label::nondet(["one", "two"]),
                Label::error("end"),
            ],
        ],
    };
    for config in [
        Config::default(),
        Config::default().collect_errors(),
        Config::default().with_max_sends(2),
        Config {
            max_executions: Some(2),
            ..Config::default().collect_errors()
        },
    ] {
        let snapshots = ParentSnapshots::default();
        let mut program = program.clone();
        if config.max_executions.is_some() {
            // Full terminals exercise the execution-cap stop; error terminals
            // deliberately do not count against max_executions.
            program.threads[2].pop();
        }
        explore(|| program.clone(), &snapshots, config);
        assert!(snapshots.visits.load(Ordering::Relaxed) > 1);
        assert!(snapshots.stack.lock().unwrap().is_empty());
    }
}

#[test]
fn graph_agnostic_rf_trials_preserve_metadata_counts_and_terminal_graphs() {
    use must::{Execution, ExecutionKind};
    use std::sync::Mutex;

    #[derive(Default)]
    struct TrialLog {
        counts: CountingObserver,
        metadata: Mutex<Vec<String>>,
        terminals: Mutex<BTreeSet<String>>,
    }
    impl Observer for TrialLog {
        fn inspects_rf_trial_graphs(&self) -> bool {
            false
        }
        fn inspects_revisit_targets(&self) -> bool {
            false
        }
        fn on_event_added(&self, g: &ExecutionGraph, e: EventId) {
            self.counts.on_event_added(g, e);
            self.metadata.lock().unwrap().push(format!("event {e:?}"));
        }
        fn on_rf_choice(&self, g: &ExecutionGraph, r: EventId, src: Option<EventId>) {
            self.counts.on_rf_choice(g, r, src);
            self.metadata
                .lock()
                .unwrap()
                .push(format!("rf {r:?} {src:?}"));
        }
        fn on_inconsistent(&self, g: &ExecutionGraph) {
            self.counts.on_inconsistent(g);
            self.metadata.lock().unwrap().push("inconsistent".into());
        }
        fn on_revisit_candidate(
            &self,
            _g: &ExecutionGraph,
            r: EventId,
            s: EventId,
            _target: &ExecutionGraph,
        ) {
            self.metadata
                .lock()
                .unwrap()
                .push(format!("candidate {r:?} {s:?}"));
        }
        fn on_revisit_arm_rejected(
            &self,
            _g: &ExecutionGraph,
            r: EventId,
            s: EventId,
            _target: &ExecutionGraph,
            ep: EventId,
        ) {
            self.metadata
                .lock()
                .unwrap()
                .push(format!("arm {r:?} {s:?} {ep:?}"));
        }
        fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
            self.counts.on_revisit_rejected(g, r, s);
            self.metadata
                .lock()
                .unwrap()
                .push(format!("rejected {r:?} {s:?}"));
        }
        fn on_backward_revisit(
            &self,
            g: &ExecutionGraph,
            r: EventId,
            s: EventId,
            deleted: &BTreeSet<EventId>,
        ) {
            self.counts.on_backward_revisit(g, r, s, deleted);
            self.metadata
                .lock()
                .unwrap()
                .push(format!("backward {r:?} {s:?} {deleted:?}"));
        }
        fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
            self.counts.on_execution(exec, kind);
            let key = format!("{kind:?}:{}", exec.graph().canonical_key());
            self.metadata.lock().unwrap().push(key.clone());
            self.terminals.lock().unwrap().insert(key);
        }
    }
    // This wrapper uses the default capability and forces the pre-optimization
    // materialized path while forwarding identical metadata to the reference log.
    struct Materialized<'a>(&'a TrialLog);
    impl Observer for Materialized<'_> {
        fn on_event_added(&self, g: &ExecutionGraph, e: EventId) {
            self.0.on_event_added(g, e);
        }
        fn on_rf_choice(&self, g: &ExecutionGraph, r: EventId, src: Option<EventId>) {
            assert_eq!(g.reads_from(r), src);
            self.0.on_rf_choice(g, r, src);
        }
        fn on_inconsistent(&self, g: &ExecutionGraph) {
            self.0.on_inconsistent(g);
        }
        fn on_revisit_candidate(
            &self,
            g: &ExecutionGraph,
            r: EventId,
            s: EventId,
            target: &ExecutionGraph,
        ) {
            let prefix = g.porf_prefix(s);
            let keep = g
                .iter_events()
                .filter(|&x| g.stamp(x) <= g.stamp(r) || prefix.contains(&x) || x == s)
                .collect();
            let mut expected = g.restrict(&keep);
            expected.set_rf(r, Some(s));
            assert_eq!(target.canonical_key(), expected.canonical_key());
            self.0.on_revisit_candidate(g, r, s, target);
        }
        fn on_revisit_arm_rejected(
            &self,
            g: &ExecutionGraph,
            r: EventId,
            s: EventId,
            target: &ExecutionGraph,
            ep: EventId,
        ) {
            assert_eq!(target.reads_from(r), Some(s));
            self.0.on_revisit_arm_rejected(g, r, s, target, ep);
        }
        fn on_revisit_rejected(&self, g: &ExecutionGraph, r: EventId, s: EventId) {
            self.0.on_revisit_rejected(g, r, s);
        }
        fn on_backward_revisit(
            &self,
            g: &ExecutionGraph,
            r: EventId,
            s: EventId,
            deleted: &BTreeSet<EventId>,
        ) {
            self.0.on_backward_revisit(g, r, s, deleted);
        }
        fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
            self.0.on_execution(exec, kind);
        }
    }

    let mut backwards = 0;
    let mut rejected = 0;
    for model in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
        let program = SeqProgram {
            threads: vec![
                vec![
                    Label::send(model, 2, "a"),
                    Label::send(model, 1, "other"),
                    Label::send(model, 99, "outside"),
                ],
                vec![Label::send(model, 2, "b"), recv()],
                vec![
                    Label::recv_nb(Pred::any()),
                    Label::recv(Pred::new("selective", |v| v == "a")),
                    Label::error("end"),
                ],
            ],
        };
        let base = Config::default()
            .collect_errors()
            .with_priorities(vec![2, 1, 0]);
        let mut configs = vec![
            base.clone(),
            base.clone()
                .with_source_order(must::SourceOrder::SelfSendFirst),
        ];
        if matches!(model, Model::Asyn | Model::P2p) {
            configs.extend([
                base.clone().with_time_filter(),
                base.clone().with_time_zombie(),
                base.with_time_predicate(),
            ]);
        }
        for (config_index, config) in configs.into_iter().enumerate() {
            let fast = TrialLog::default();
            let reference = TrialLog::default();
            let materialized = Materialized(&reference);
            assert!(!fast.inspects_rf_trial_graphs());
            assert!(fast.observes_rejected_rf_trials());
            assert!(materialized.observes_rejected_rf_trials());
            assert!(materialized.inspects_rf_trial_graphs());
            explore(|| program.clone(), &fast, config.clone());
            explore(|| program.clone(), &materialized, config);
            assert_eq!(
                *fast.metadata.lock().unwrap(),
                *reference.metadata.lock().unwrap()
            );
            assert_eq!(
                *fast.terminals.lock().unwrap(),
                *reference.terminals.lock().unwrap()
            );
            assert_eq!(fast.counts.events_added(), reference.counts.events_added());
            assert_eq!(fast.counts.rf_choices(), reference.counts.rf_choices());
            assert_eq!(fast.counts.inconsistent(), reference.counts.inconsistent());
            assert_eq!(
                fast.counts.backward_revisits(),
                reference.counts.backward_revisits()
            );
            assert_eq!(
                fast.counts.revisits_rejected(),
                reference.counts.revisits_rejected()
            );
            if model == Model::Asyn && config_index == 0 {
                assert!(fast.counts.backward_revisits() > 0);
                assert!(fast.counts.revisits_rejected() > 0);
            }
            backwards += fast.counts.backward_revisits();
            rejected += fast.counts.revisits_rejected();
            assert!(fast.counts.inconsistent() > 0);
            assert!(!fast.terminals.lock().unwrap().is_empty());
        }
    }
    assert!(backwards > 0);
    assert!(rejected > 0);
}

#[test]
fn default_revisit_target_capability_is_conservative_even_with_ignored_rf_graphs() {
    #[derive(Default)]
    struct TargetInspector(AtomicUsize);
    impl Observer for TargetInspector {
        fn inspects_rf_trial_graphs(&self) -> bool {
            false
        }
        fn on_revisit_candidate(
            &self,
            host: &ExecutionGraph,
            r: EventId,
            s: EventId,
            target: &ExecutionGraph,
        ) {
            assert_eq!(target.reads_from(r), Some(s));
            assert_ne!(host.reads_from(r), target.reads_from(r));
            assert!(must::consistent(target));
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }
    let program = SeqProgram {
        threads: vec![
            vec![Label::send(Model::Asyn, 2, "a")],
            vec![Label::send(Model::Asyn, 2, "b")],
            vec![recv()],
        ],
    };
    let observer = (
        must::EventCountingObserver::default(),
        TargetInspector::default(),
    );
    assert!(!observer.inspects_rf_trial_graphs());
    assert!(observer.inspects_revisit_targets());
    explore(
        || program.clone(),
        &observer,
        Config::default().with_priorities(vec![2, 0, 1]),
    );
    assert!(observer.1 .0.load(Ordering::Relaxed) > 0);
    assert_eq!(observer.0.full(), 2);
}

#[test]
fn graph_inspecting_observer_in_a_tuple_keeps_exact_rejected_rf_snapshots() {
    use must::observer::{NullObserver, RecordingObserver, StepKind};

    let program = SeqProgram {
        threads: vec![
            vec![send(2, "a"), send(99, "outside")],
            vec![send(2, "b")],
            vec![recv()],
        ],
    };
    let observers = (CountingObserver::default(), RecordingObserver::new());
    assert!(!NullObserver.inspects_rf_trial_graphs());
    assert!(!observers.0.inspects_rf_trial_graphs());
    assert!(observers.inspects_rf_trial_graphs());
    explore(|| program.clone(), &observers, Config::default());
    let mut rejected_wrong_destination = false;
    let mut rejected_blocking_bottom = false;
    for step in observers.1.steps() {
        match step.kind {
            StepKind::RfChoice { r, src } => {
                assert_eq!(step.graph.reads_from(r), src);
                rejected_wrong_destination |=
                    src.is_some_and(|s| step.graph.label(s).dst() == Some(99));
                rejected_blocking_bottom |= src.is_none();
            }
            StepKind::Inconsistent => assert!(!must::consistency::consistent(&step.graph)),
            _ => {}
        }
    }
    assert!(rejected_wrong_destination);
    assert!(rejected_blocking_bottom);
}

#[test]
fn rejected_rf_trial_capability_is_independent_and_composes_conservatively() {
    use must::observer::{EventCountingObserver, NullObserver, RecordingObserver};
    #[derive(Default)]
    struct MetadataCounter(AtomicUsize);
    impl Observer for MetadataCounter {
        fn inspects_rf_trial_graphs(&self) -> bool {
            false
        }
        fn on_rf_choice(&self, _: &ExecutionGraph, _: EventId, _: Option<EventId>) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }
    assert!(!NullObserver.observes_rejected_rf_trials());
    assert!(!EventCountingObserver::default().observes_rejected_rf_trials());
    assert!(CountingObserver::default().observes_rejected_rf_trials());
    assert!(RecordingObserver::new().observes_rejected_rf_trials());
    assert!(!(NullObserver, EventCountingObserver::default()).observes_rejected_rf_trials());
    let observers = (EventCountingObserver::default(), MetadataCounter::default());
    assert!(!observers.inspects_rf_trial_graphs());
    assert!(observers.observes_rejected_rf_trials());
    let program = SeqProgram {
        threads: vec![
            vec![send(1, "a"), send(1, "b"), send(99, "outside")],
            vec![recv(), recv()],
        ],
    };
    let reference = CountingObserver::default();
    explore(|| program.clone(), &observers, Config::default());
    explore(|| program.clone(), &reference, Config::default());
    assert_eq!(
        observers.1 .0.load(Ordering::Relaxed),
        reference.rf_choices()
    );
    assert!(reference.inconsistent() > 0);
}

#[test]
fn indexed_unread_sources_preserve_terminal_multisets_events_and_cutoffs() {
    use must::{Execution, ExecutionKind, SourceOrder, Window};
    use std::sync::Mutex;

    struct Outcomes {
        indexed: bool,
        events: AtomicUsize,
        bottoms: AtomicUsize,
        terminals: Mutex<BTreeMap<String, usize>>,
        cuts: Mutex<BTreeMap<String, usize>>,
    }
    impl Outcomes {
        fn new(indexed: bool) -> Self {
            Self {
                indexed,
                events: AtomicUsize::new(0),
                bottoms: AtomicUsize::new(0),
                terminals: Mutex::new(BTreeMap::new()),
                cuts: Mutex::new(BTreeMap::new()),
            }
        }
    }
    impl Observer for Outcomes {
        fn observes_rejected_rf_trials(&self) -> bool {
            !self.indexed
        }
        fn inspects_rf_trial_graphs(&self) -> bool {
            false
        }
        fn inspects_revisit_targets(&self) -> bool {
            false
        }
        fn on_event_added(&self, _: &ExecutionGraph, _: EventId) {
            self.events.fetch_add(1, Ordering::Relaxed);
        }
        fn on_execution(&self, execution: &Execution, kind: ExecutionKind) {
            let key = format!(
                "{kind:?}:{}:{:?}",
                execution.canonical_key(),
                execution.labels()
            );
            *self.terminals.lock().unwrap().entry(key).or_default() += 1;
            if execution
                .graph()
                .iter_recvs()
                .any(|r| execution.graph().reads_from(r).is_none())
            {
                self.bottoms.fetch_add(1, Ordering::Relaxed);
            }
        }
        fn on_send_limit(&self, graph: &ExecutionGraph, limit: usize) {
            let key = format!("{limit}:{}", graph.canonical_key());
            *self.cuts.lock().unwrap().entry(key).or_default() += 1;
        }
    }
    fn compare(program: &SeqProgram, config: Config) -> usize {
        let indexed = Outcomes::new(true);
        let reference = Outcomes::new(false);
        explore(|| program.clone(), &indexed, config.clone());
        explore(|| program.clone(), &reference, config);
        assert_eq!(
            *indexed.terminals.lock().unwrap(),
            *reference.terminals.lock().unwrap()
        );
        assert_eq!(
            *indexed.cuts.lock().unwrap(),
            *reference.cuts.lock().unwrap()
        );
        assert_eq!(
            indexed.events.load(Ordering::Relaxed),
            reference.events.load(Ordering::Relaxed)
        );
        assert_eq!(
            indexed.bottoms.load(Ordering::Relaxed),
            reference.bottoms.load(Ordering::Relaxed)
        );
        indexed.bottoms.load(Ordering::Relaxed)
    }
    for model in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
        let program = SeqProgram {
            threads: vec![
                vec![
                    Label::send(model, 2, "a"),
                    Label::send(model, 1, "other"),
                    Label::send(model, 99, "outside"),
                ],
                vec![Label::send(model, 2, "b"), recv()],
                vec![
                    Label::recv_nb(Pred::any()),
                    Label::recv(Pred::eq("a")),
                    Label::error("end"),
                ],
            ],
        };
        let base = Config::default()
            .collect_errors()
            .with_priorities(vec![2, 1, 0]);
        assert!(
            compare(&program, base.clone()) > 0,
            "nonblocking bottom must remain for {model:?}"
        );
        for order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
            for threads in [1, 4] {
                compare(
                    &program,
                    base.clone().with_source_order(order).with_threads(threads),
                );
            }
        }
        compare(&program, base.clone().with_max_sends(2));
        if matches!(model, Model::Asyn | Model::P2p) {
            compare(&program, base.clone().with_time_filter());
            compare(&program, base.clone().with_time_zombie());
            compare(&program, base.with_time_predicate());
        }
    }
    // The destination index and the source snapshot both exceed the inline capacity.
    let mut many = vec![Label::send(Model::Asyn, 1, "message"); 35];
    many.push(Label::send(Model::Asyn, 99, "outside"));
    let program = SeqProgram {
        threads: vec![many, vec![Label::recv_nb(Pred::any())]],
    };
    assert!(compare(&program, Config::default().with_priorities(vec![1, 0])) > 0);

    let timed = SeqProgram {
        threads: vec![
            vec![
                Label::send_within(Model::P2p, 1, "a", Window::new(0, 2)),
                Label::send_within(Model::P2p, 99, "outside", Window::new(0, 2)),
            ],
            vec![Label::recv_timeout_timed(Pred::eq("a"), Window::new(2, 3))],
        ],
    };
    compare(
        &timed,
        Config::default()
            .collect_errors()
            .with_mailbox_time()
            .with_time_filter()
            .with_priorities(vec![1, 0]),
    );
}

#[test]
fn continuation_sidecars_match_plain_replay_across_branches_cuts_and_eviction() {
    use must::{Execution, ExecutionKind, ProgramCursor, SourceOrder, Tid, TraceLabel, Window};
    use std::cell::{Cell, RefCell};
    use std::sync::{Arc, Mutex};

    #[derive(Clone)]
    struct Decisions {
        model: Model,
    }
    impl Program for Decisions {
        fn num_threads(&self) -> usize {
            3
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            traces
                .iter()
                .enumerate()
                .map(|(tid, trace)| self.next_thread(tid, trace))
                .collect()
        }
        fn next_thread(&self, tid: Tid, trace: &[Option<Val>]) -> ThreadNext {
            let next = match (tid, trace.len()) {
                (0, 0) => Label::send(self.model, 2, "a"),
                (0, 1) => Label::recv_nb(Pred::new("echo", |v| v.starts_with("echo:"))),
                (1, 0) => Label::send(self.model, 2, "b"),
                (1, 1) => Label::send(self.model, 99, "outside"),
                (2, 0) => Label::recv_nb(Pred::any()),
                (2, 1) => Label::recv(Pred::any()),
                (2, 2) => {
                    let value = trace[0].map_or("bottom", must::intern::resolve);
                    Label::send(self.model, 0, format!("echo:{value}"))
                }
                (2, 3) => Label::nondet(["x", "y"]),
                (2, 4) => Label::error(format!("end:{}", must::intern::resolve(trace[3].unwrap()))),
                _ => return ThreadNext::Finished,
            };
            ThreadNext::Next(next)
        }
        fn labels(&self, traces: &[Vec<Option<Val>>]) -> Vec<TraceLabel> {
            traces
                .iter()
                .enumerate()
                .flat_map(|(tid, trace)| {
                    trace
                        .iter()
                        .enumerate()
                        .filter_map(move |(position, value)| {
                            value.map(|value| TraceLabel {
                                tid,
                                position: position + 1,
                                value,
                            })
                        })
                })
                .collect()
        }
    }

    #[derive(Default)]
    struct Calls {
        replay: AtomicUsize,
        advanced: AtomicUsize,
        refused: AtomicUsize,
    }
    struct Handles<P> {
        inner: P,
        owner: u64,
        epoch: Cell<u64>,
        attempts: Cell<usize>,
        evict: bool,
        states: RefCell<Vec<(Tid, Vec<Option<Val>>)>>,
        calls: Arc<Calls>,
    }
    impl<P: Program> Handles<P> {
        fn new(inner: P, evict: bool, calls: Arc<Calls>) -> Self {
            static OWNER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
            Self {
                inner,
                owner: OWNER.fetch_add(1, Ordering::Relaxed),
                epoch: Cell::new(1),
                attempts: Cell::new(0),
                evict,
                states: RefCell::new(Vec::new()),
                calls,
            }
        }
        fn remember(&self, tid: Tid, trace: Vec<Option<Val>>) -> ProgramCursor {
            let mut states = self.states.borrow_mut();
            let index = states.len();
            states.push((tid, trace));
            ProgramCursor::new([self.owner, self.epoch.get(), index as u64])
        }
    }
    impl<P: Program> Program for Handles<P> {
        fn num_threads(&self) -> usize {
            self.inner.num_threads()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.inner.next(traces)
        }
        fn next_thread(&self, tid: Tid, trace: &[Option<Val>]) -> ThreadNext {
            self.inner.next_thread(tid, trace)
        }
        fn labels(&self, traces: &[Vec<Option<Val>>]) -> Vec<TraceLabel> {
            self.inner.labels(traces)
        }
        fn next_thread_cursor(
            &self,
            tid: Tid,
            trace: &[Option<Val>],
        ) -> (ThreadNext, Option<ProgramCursor>) {
            self.calls.replay.fetch_add(1, Ordering::Relaxed);
            (
                self.inner.next_thread(tid, trace),
                Some(self.remember(tid, trace.to_vec())),
            )
        }
        fn advance_thread(
            &self,
            tid: Tid,
            cursor: ProgramCursor,
            entry: Option<Val>,
        ) -> Option<(ThreadNext, ProgramCursor)> {
            let attempt = self.attempts.get() + 1;
            self.attempts.set(attempt);
            if self.evict && attempt % 3 == 0 {
                self.epoch.set(self.epoch.get() + 1);
                self.states.borrow_mut().clear();
            }
            let [owner, epoch, index] = cursor.words();
            let state = if owner == self.owner && epoch == self.epoch.get() {
                self.states
                    .borrow()
                    .get(usize::try_from(index).ok()?)
                    .filter(|(thread, _)| *thread == tid)
                    .cloned()
            } else {
                None
            };
            let Some((_, mut trace)) = state else {
                self.calls.refused.fetch_add(1, Ordering::Relaxed);
                return None;
            };
            trace.push(entry);
            let next = self.inner.next_thread(tid, &trace);
            let cursor = self.remember(tid, trace);
            self.calls.advanced.fetch_add(1, Ordering::Relaxed);
            Some((next, cursor))
        }
    }
    struct Plain<P>(P);
    impl<P: Program> Program for Plain<P> {
        fn num_threads(&self) -> usize {
            self.0.num_threads()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.0.next(traces)
        }
        fn next_thread(&self, tid: Tid, trace: &[Option<Val>]) -> ThreadNext {
            self.0.next_thread(tid, trace)
        }
        fn labels(&self, traces: &[Vec<Option<Val>>]) -> Vec<TraceLabel> {
            self.0.labels(traces)
        }
    }
    #[derive(Default)]
    struct Results {
        events: AtomicUsize,
        terminals: Mutex<BTreeMap<String, usize>>,
        cuts: Mutex<BTreeMap<String, usize>>,
    }
    impl Observer for Results {
        fn observes_rejected_rf_trials(&self) -> bool {
            false
        }
        fn inspects_rf_trial_graphs(&self) -> bool {
            false
        }
        fn inspects_revisit_targets(&self) -> bool {
            false
        }
        fn on_event_added(&self, _: &ExecutionGraph, _: EventId) {
            self.events.fetch_add(1, Ordering::Relaxed);
        }
        fn on_execution(&self, execution: &Execution, kind: ExecutionKind) {
            let key = format!(
                "{kind:?}:{}:{:?}",
                execution.canonical_key(),
                execution.labels()
            );
            *self.terminals.lock().unwrap().entry(key).or_default() += 1;
        }
        fn on_send_limit(&self, graph: &ExecutionGraph, limit: usize) {
            *self
                .cuts
                .lock()
                .unwrap()
                .entry(format!("{limit}:{}", graph.canonical_key()))
                .or_default() += 1;
        }
    }
    fn compare<P: Program + Clone + Sync>(
        program: P,
        config: Config,
        evict: bool,
        calls: &Arc<Calls>,
    ) {
        let resumed = Results::default();
        let reference = Results::default();
        explore(
            || Handles::new(program.clone(), evict, Arc::clone(calls)),
            &resumed,
            config.clone(),
        );
        explore(|| Plain(program.clone()), &reference, config);
        assert_eq!(
            *resumed.terminals.lock().unwrap(),
            *reference.terminals.lock().unwrap()
        );
        assert_eq!(
            *resumed.cuts.lock().unwrap(),
            *reference.cuts.lock().unwrap()
        );
        assert_eq!(
            resumed.events.load(Ordering::Relaxed),
            reference.events.load(Ordering::Relaxed)
        );
    }
    let calls = Arc::new(Calls::default());
    for model in [Model::Asyn, Model::P2p, Model::Cd, Model::Mbox] {
        let program = Decisions { model };
        let base = Config::default()
            .collect_errors()
            .with_priorities(vec![2, 1, 0]);
        for evict in [false, true] {
            for order in [SourceOrder::EventId, SourceOrder::SelfSendFirst] {
                for threads in [1, 4] {
                    compare(
                        program.clone(),
                        base.clone().with_source_order(order).with_threads(threads),
                        evict,
                        &calls,
                    );
                }
            }
            compare(
                program.clone(),
                base.clone().with_max_sends(3),
                evict,
                &calls,
            );
            compare(
                program.clone(),
                Config {
                    max_executions: Some(2),
                    ..base.clone()
                },
                evict,
                &calls,
            );
            compare(
                program.clone(),
                Config::default().with_priorities(vec![2, 1, 0]),
                evict,
                &calls,
            );
        }
        if matches!(model, Model::Asyn | Model::P2p) {
            compare(
                program.clone(),
                base.clone().with_time_filter(),
                true,
                &calls,
            );
            compare(
                program.clone(),
                base.clone().with_time_zombie(),
                true,
                &calls,
            );
            compare(program, base.with_time_predicate(), true, &calls);
        }
    }
    let timed = SeqProgram {
        threads: vec![
            vec![Label::send_within(Model::P2p, 1, "a", Window::new(0, 2))],
            vec![Label::recv_timeout_timed(Pred::eq("a"), Window::new(2, 3))],
        ],
    };
    compare(
        timed,
        Config::default()
            .collect_errors()
            .with_mailbox_time()
            .with_time_filter()
            .with_priorities(vec![1, 0]),
        true,
        &calls,
    );
    assert!(calls.replay.load(Ordering::Relaxed) > 0);
    assert!(calls.advanced.load(Ordering::Relaxed) > 0);
    assert!(calls.refused.load(Ordering::Relaxed) > 0);
}
