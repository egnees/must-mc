//! Oracle tests for the eager-time realizability filter (`Config::with_time_filter`,
//! engine_plan §5.б). Each hand-picked program pins the `(full, blocked, filtered)` split;
//! the numbers were validated independently (the integer-enumeration reference in
//! `common::time_feasible_ref`, cross-checked here on the tricky cases and swept over a
//! random corpus in `fuzz_timed.rs`). Per CLAUDE.md discipline, a mismatch is a filter or
//! reference bug — the number is never edited to fit.
//!
//! Time semantics recap (engine_plan §0): a send `s` with window `[lo, hi]` arrives at
//! `arr(s) ∈ occ(s) + [lo, hi]`; `avail` is `arr` for asyn and the channel-prefix max for
//! p2p; a blocking receive reading `s` fires at `max(occ(r), avail(s))` and is realizable
//! iff either `avail(s) ≤ occ(r)` (the message waited — competitors ignored) or every
//! competing send is at least as available as `s`.

mod common;

use std::collections::BTreeSet;

use common::{
    assert_timed_invariant, blocked_and_full, blocked_no_match, example_2_8, factorial, ns_nr,
    ns_nr_sel, ns_r, nworkers, permutations, recv, recv_eq, send, ssr, time_feasible_ref,
    SeqProgram,
};
use must::event::{Label, Model, Window};
use must::{
    check, eager_feasible, explore, Config, CountingObserver, Ctx, ExecutionCollector,
    ExecutionGraph, Program, System,
};

// -- helpers ----------------------------------------------------------------------

/// A send with a finite delivery window `[lo, hi]`.
fn tsend(model: Model, dst: usize, v: &str, lo: u64, hi: u64) -> Label {
    Label::send_within(model, dst, v, Window::new(lo, hi))
}

/// Explore `prog` under the eager time filter (plus its required companion
/// `collect_errors`), returning the `(counter, collector)` pair.
fn run_filtered(prog: &SeqProgram, perm: &[usize]) -> (CountingObserver, ExecutionCollector) {
    let obs = (CountingObserver::new(), ExecutionCollector::new());
    explore(
        || prog.clone(),
        &obs,
        Config::default()
            .collect_errors()
            .with_time_filter()
            .with_priorities(perm.to_vec()),
    );
    obs
}

/// The time-filter split of `prog`, asserted invariant across every priority permutation
/// (and free of duplicate terminal / filtered keys). Panics on any per-permutation drift.
struct Counts {
    full: usize,
    blocked: usize,
    filtered_full: usize,
    filtered_blocked: usize,
    filtered_errors: usize,
    full_keys: BTreeSet<String>,
    filtered_keys: BTreeSet<String>,
}

fn timed_counts(prog: &SeqProgram) -> Counts {
    let n = prog.num_threads();
    let mut reference: Option<Counts> = None;
    for perm in permutations(n) {
        let (cnt, col) = run_filtered(prog, &perm);

        let tkeys = col.terminal_keys();
        let tset: BTreeSet<String> = tkeys.iter().cloned().collect();
        assert_eq!(
            tkeys.len(),
            tset.len(),
            "duplicate terminal keys under {perm:?}"
        );
        let fkeys = col.filtered_keys();
        let fset: BTreeSet<String> = fkeys.iter().cloned().collect();
        assert_eq!(
            fkeys.len(),
            fset.len(),
            "duplicate filtered keys under {perm:?}"
        );

        let c = Counts {
            full: col.full_count(),
            blocked: col.blocked_count(),
            filtered_full: cnt.filtered_full(),
            filtered_blocked: cnt.filtered_blocked(),
            filtered_errors: cnt.filtered_errors(),
            full_keys: col.full_keys().into_iter().collect(),
            filtered_keys: fset,
        };
        match &reference {
            None => reference = Some(c),
            Some(r) => {
                assert_eq!(c.full, r.full, "full differs under {perm:?}");
                assert_eq!(c.blocked, r.blocked, "blocked differs under {perm:?}");
                assert_eq!(
                    c.filtered_full, r.filtered_full,
                    "filtered_full differs under {perm:?}"
                );
                assert_eq!(
                    c.filtered_blocked, r.filtered_blocked,
                    "filtered_blocked differs under {perm:?}"
                );
                assert_eq!(
                    c.filtered_errors, r.filtered_errors,
                    "filtered_errors differs under {perm:?}"
                );
                assert_eq!(c.full_keys, r.full_keys, "full_keys differ under {perm:?}");
                assert_eq!(
                    c.filtered_keys, r.filtered_keys,
                    "filtered_keys differ under {perm:?}"
                );
            }
        }
    }
    reference.expect("at least one permutation")
}

/// Whether some full execution has a receive reading a send whose value is `v`.
fn full_reads_value(col: &ExecutionCollector, v: &str) -> bool {
    col.full().iter().any(|e| {
        let g = e.graph();
        g.recvs().into_iter().any(|r| {
            g.reads_from(r)
                .map(|s| g.label(s).val() == Some(v))
                .unwrap_or(false)
        })
    })
}

/// Cross-check the filter against the independent integer reference on every terminal of
/// an untimed run of `prog`: `eager_feasible` must agree with `time_feasible_ref` term by
/// term. Returns how many terminals are time-realizable.
fn cross_check_reference(prog: &SeqProgram) -> usize {
    let col = ExecutionCollector::new();
    explore(|| prog.clone(), &col, Config::default());
    let mut feasible = 0;
    let mut budget = 5_000_000usize;
    for exec in col.terminals() {
        let g = exec.graph();
        let reference = time_feasible_ref(g, &mut budget).expect("within budget");
        assert_eq!(
            eager_feasible(g),
            reference,
            "filter disagrees with the integer reference on:\n{}",
            exec.canonical_key()
        );
        if reference {
            feasible += 1;
        }
    }
    feasible
}

// The three-sender receive chains, shared with the parallel-determinism test.
fn chain_gap() -> SeqProgram {
    // a[10,20] < b[30,40] < c[50,100]: strictly separated windows.
    SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 3, "a", 10, 20)],
        vec![tsend(Model::Asyn, 3, "b", 30, 40)],
        vec![tsend(Model::Asyn, 3, "c", 50, 100)],
        vec![recv(), recv(), recv()],
    ])
}

fn chain_touching() -> SeqProgram {
    // a[10,20], b[20,40], c[40,100]: windows meet at 20 and 40 (closed, non-strict ≥).
    SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 3, "a", 10, 20)],
        vec![tsend(Model::Asyn, 3, "b", 20, 40)],
        vec![tsend(Model::Asyn, 3, "c", 40, 100)],
        vec![recv(), recv(), recv()],
    ])
}

// -- 1. two senders, disjoint windows: only the earlier message is readable ----------

#[test]
fn timed_ssr_gap() {
    // T0: a[10,20] -> 2  ||  T1: b[30,40] -> 2  ||  T2: recv()
    // Reading b needs its competitor a to be as-late-as b (avail(a) ≤ 20 < 30 ≤ avail(b)),
    // impossible — so b's reading is time-infeasible.
    let prog = SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 2, "a", 10, 20)],
        vec![tsend(Model::Asyn, 2, "b", 30, 40)],
        vec![recv()],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(c.full, 1, "reads a only");
    assert_eq!(c.filtered_full, 1, "reading b is time-infeasible");
    assert_eq!(c.blocked, 0);
    assert_eq!(cross_check_reference(&prog), 1);
}

// -- 2. touching windows: closed intervals meet, both readable (non-strict ≥) --------

#[test]
fn timed_ssr_touching() {
    // a[10,20] / b[20,40]: avail(a)=avail(b)=20 is admissible, so both readings survive.
    let prog = SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 2, "a", 10, 20)],
        vec![tsend(Model::Asyn, 2, "b", 20, 40)],
        vec![recv()],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(
        c.full, 2,
        "both readings realizable via the touching point 20"
    );
    assert_eq!(c.filtered_full, 0);
    assert_eq!(cross_check_reference(&prog), 2);
}

// -- 3. three-sender chain, disjoint windows: exactly one delivery order --------------

#[test]
fn timed_chain_gap() {
    let prog = chain_gap();
    let c = timed_counts(&prog);
    // Only the increasing order a,b,c is realizable; the other 5 of 3! are cut.
    assert_eq!(c.full, 1, "only a,b,c");
    assert_eq!(c.filtered_full, 5);
    assert_eq!(cross_check_reference(&prog), 1);
}

// -- 4. three-sender chain, touching windows: three orders (the delicate = 3, not 4) -

#[test]
fn timed_chain_touching() {
    let prog = chain_touching();
    let c = timed_counts(&prog);
    // abc; acb (via avail(b)=avail(c)=40); bac (via avail(a)=avail(b)=20). bca/cab/cba are
    // cut. The value 3 is confirmed by the independent integer reference below.
    assert_eq!(c.full, 3, "abc, acb, bac");
    assert_eq!(c.filtered_full, 3);
    assert_eq!(
        cross_check_reference(&prog),
        3,
        "the integer reference must also see exactly 3 realizable orders"
    );
}

// -- 5. occ moves through a reply chain: fire(recv) becomes occ(next send) ------------

#[test]
fn timed_reply_occ_chain() {
    // T0: req[10,20]->1; recv()   ||   T1: recv(); rsp[1,5]->0   ||   T2: late[20,100]->0
    // T1 reads req and fires at avail(req) ∈ [10,20]; rsp then leaves at occ(rsp)+[1,5] =
    // [11,25]. T0's recv reads rsp or late.
    let reply = |lo: u64, hi: u64, late_lo: u64| {
        SeqProgram::new(vec![
            vec![tsend(Model::Asyn, 1, "req", 10, 20), recv()],
            vec![recv(), tsend(Model::Asyn, 0, "rsp", lo, hi)],
            vec![tsend(Model::Asyn, 0, "late", late_lo, 100)],
        ])
    };

    // rsp ∈ [11,25] overlaps late ∈ [20,100]: both readings survive.
    let c = timed_counts(&reply(1, 5, 20));
    assert_eq!(c.full, 2, "rsp and late both readable");
    assert_eq!(c.filtered_full, 0);
    assert_eq!(cross_check_reference(&reply(1, 5, 20)), 2);

    // late pushed to [40,100]: rsp ≤ 25 < 40, so reading late is infeasible.
    let c = timed_counts(&reply(1, 5, 40));
    assert_eq!(c.full, 1, "only rsp");
    assert_eq!(c.filtered_full, 1);
    assert_eq!(cross_check_reference(&reply(1, 5, 40)), 1);

    // rsp[0,0]: arr(rsp) = occ(rsp) ∈ [10,20], touching late's floor at 20 — both readable.
    let c = timed_counts(&reply(0, 0, 20));
    assert_eq!(c.full, 2, "touching at 20");
    assert_eq!(c.filtered_full, 0);
}

// -- 6. corrected B-clause: a po-later reader keeps a send a live competitor ----------

#[test]
fn timed_b_clause_late_reader() {
    // T0: x[1,1]->2  ||  T1: y[50,50]->2  ||  T2: recv(); recv().
    // Assignment r1<-y, r2<-x: x is read by the po-*later* r2, so it is NOT consumed at r1
    // and stays a competitor of r1 — B then demands avail(x)=1 ≥ avail(y)=50, false.
    let prog = SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 2, "x", 1, 1)],
        vec![tsend(Model::Asyn, 2, "y", 50, 50)],
        vec![recv(), recv()],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(c.full, 1, "only r1<-x, r2<-y");
    assert_eq!(
        c.filtered_full, 1,
        "r1<-y, r2<-x is infeasible (late-reader competitor)"
    );

    // Direct assertion on the hand-built infeasible graph.
    let mut g = ExecutionGraph::new();
    let x = g.add_event(0, tsend(Model::Asyn, 2, "x", 1, 1));
    let y = g.add_event(1, tsend(Model::Asyn, 2, "y", 50, 50));
    let r1 = g.add_event(2, recv());
    let r2 = g.add_event(2, recv());
    g.set_rf(r1, Some(y));
    g.set_rf(r2, Some(x));
    assert!(!eager_feasible(&g), "r1<-y, r2<-x must be time-infeasible");
}

// -- 7. why a filter, not a consistency predicate (Conditional-Extensibility ctr-ex) -

#[test]
fn timed_extensibility_counterexample() {
    // T0: s[1,2]->2  ||  T1: m[40,60]->2  ||  T2: recv().
    // Reading the late m is cut by the early competitor s; reading s is fine (m is a free
    // competitor, 40 ≥ 2). This is exactly the extension that breaks Conditional
    // Extensibility (§3.2.1) — hence an eager *filter*, not a consistency predicate.
    let prog = SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 2, "s", 1, 2)],
        vec![tsend(Model::Asyn, 2, "m", 40, 60)],
        vec![recv()],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(c.full, 1);
    assert_eq!(c.filtered_full, 1);

    let mut g = ExecutionGraph::new();
    let s = g.add_event(0, tsend(Model::Asyn, 2, "s", 1, 2));
    let m = g.add_event(1, tsend(Model::Asyn, 2, "m", 40, 60));
    let r = g.add_event(2, recv());
    g.set_rf(r, Some(m));
    assert!(!eager_feasible(&g), "reading m is time-infeasible");
    g.set_rf(r, Some(s));
    assert!(eager_feasible(&g), "reading s is realizable");
}

// -- 8. error gating (runtime): a time-infeasible error terminal is suppressed --------

#[test]
fn timed_error_gating() {
    // T0: x[1,1]->2  ||  T1: y[50,50]->2  ||  T2: v=recv(); assert(v != "y").
    // Reading y (the violating message) is time-infeasible (competitor x is strictly
    // earlier), so the only error terminal is suppressed under the filter.
    // A `fn` item (Copy) so it can drive two explore runs by value.
    fn make() -> System {
        let mut sys = System::new();
        sys.add(|c: Ctx| async move {
            c.send_within(2, "x", Model::Asyn, Window::new(1, 1));
        });
        sys.add(|c: Ctx| async move {
            c.send_within(2, "y", Model::Asyn, Window::new(50, 50));
        });
        sys.add(|c: Ctx| async move {
            let v = c.recv(|_| true).await;
            c.assert_that(v != "y", "must not read y");
        });
        sys
    }

    // Untimed (collect_errors, no filter): 1 full (reads x) + 1 error (reads y).
    let col = ExecutionCollector::new();
    explore(make, &col, Config::default().collect_errors());
    assert_eq!(col.full_count(), 1, "untimed: reads x");
    assert_eq!(col.error_count(), 1, "untimed: reads y -> assertion error");

    // With the filter: the error terminal moves to filtered_errors, errors() drops to 0.
    let obs = (CountingObserver::new(), ExecutionCollector::new());
    explore(
        make,
        &obs,
        Config::default().collect_errors().with_time_filter(),
    );
    let (cnt, col) = obs;
    assert_eq!(col.full_count(), 1, "filtered: full still reads x");
    assert_eq!(
        col.error_count(),
        0,
        "filtered: the error terminal is suppressed"
    );
    assert_eq!(
        cnt.filtered_errors(),
        1,
        "the suppressed terminal is the error"
    );
    assert_eq!(cnt.filtered_full(), 0);
}

/// A timed send under a model v1 does not support (Cd/Mbox) must be rejected, not checked
/// with the wrong semantics: `channel_prefix` only knows how to order Asyn/P2p, so a cd/mbox
/// `so` order never reaches the constraint system at all.
fn cd_send_with_a_timed_window() -> System {
    let mut sys = System::new();
    sys.add(|c: Ctx| async move {
        c.send_within(1, "x", Model::Cd, Window::new(1, 5));
    });
    sys.add(|c: Ctx| async move {
        c.recv(|_| true).await;
    });
    sys
}

/// The guard holds under the T1 filter.
#[test]
#[should_panic(expected = "supports only Asyn/P2p")]
fn timed_filter_rejects_cd_sends() {
    let col = ExecutionCollector::new();
    explore(
        cd_send_with_a_timed_window,
        &col,
        Config::default().collect_errors().with_time_filter(),
    );
}

/// ...and under the T2 predicate, where it used to be reachable only through the
/// `debug_assert!` in `record` - i.e. not at all in a release build.
#[test]
#[should_panic(expected = "supports only Asyn/P2p")]
fn timed_predicate_rejects_cd_sends() {
    let col = ExecutionCollector::new();
    explore(
        cd_send_with_a_timed_window,
        &col,
        Config::default().collect_errors().with_time_predicate(),
    );
}

/// `with_time_filter()` without `collect_errors()` is unsupported and panics up front (B1).
#[test]
#[should_panic(expected = "requires collect_errors")]
fn timed_filter_requires_collect_errors() {
    let prog = ssr();
    let col = ExecutionCollector::new();
    explore(|| prog.clone(), &col, Config::default().with_time_filter());
}

/// `with_time_zombie()` without `collect_errors()` panics for the same B1 reason.
#[test]
#[should_panic(expected = "requires collect_errors")]
fn timed_zombie_requires_collect_errors() {
    let prog = ssr();
    let col = ExecutionCollector::new();
    explore(|| prog.clone(), &col, Config::default().with_time_zombie());
}

/// Zombie is mutually exclusive with the T1 filter (three distinct regimes).
#[test]
#[should_panic(expected = "mutually exclusive")]
fn timed_zombie_excludes_filter() {
    let prog = ssr();
    let col = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &col,
        Config::default()
            .collect_errors()
            .with_time_filter()
            .with_time_zombie(),
    );
}

/// Zombie is mutually exclusive with the T2 predicate.
#[test]
#[should_panic(expected = "mutually exclusive")]
fn timed_zombie_excludes_predicate() {
    let prog = ssr();
    let col = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &col,
        Config::default()
            .collect_errors()
            .with_time_predicate()
            .with_time_zombie(),
    );
}

// -- 9. vacuity: every untimed terminal is feasible via check()'s FULL path -----------

#[test]
fn untimed_vacuity_full_path() {
    let progs: Vec<(&str, SeqProgram)> = vec![
        ("ssr", ssr()),
        ("ns_r(3)", ns_r(3)),
        ("ns_nr(3)", ns_nr(3)),
        ("ns_nr_sel(3)", ns_nr_sel(3)),
        ("nworkers(3)", nworkers(3)),
        ("blocked_no_match", blocked_no_match()),
        ("blocked_and_full", blocked_and_full()),
    ];
    for (name, prog) in &progs {
        let col = ExecutionCollector::new();
        explore(|| prog.clone(), &col, Config::default());
        let mut n = 0;
        for exec in col.terminals() {
            assert!(
                check(exec.graph()).is_feasible(),
                "{name}: untimed terminal not feasible via the full path:\n{}",
                exec.canonical_key()
            );
            n += 1;
        }
        assert!(n > 0, "{name}: produced no terminals to check");
    }
}

// -- 11. the A-clause does NOT check competitors -------------------------------------

#[test]
fn timed_case_a_no_competitors() {
    // tid0: recv(=t); recv(); recv()   with senders t[100,100] (tid1), x[10,10] (tid2),
    // y[20,20] (tid3) all -> tid0. After the first recv fires at 100, x and y both arrived
    // long ago, so each later recv fires by the A-clause regardless of the other message —
    // BOTH x-then-y and y-then-x are realizable. A "always check competitors" bug would
    // reject y-then-x (avail(x)=10 < avail(y)=20) and report only 1.
    let prog = SeqProgram::new(vec![
        vec![recv_eq("t"), recv(), recv()],
        vec![tsend(Model::Asyn, 0, "t", 100, 100)],
        vec![tsend(Model::Asyn, 0, "x", 10, 10)],
        vec![tsend(Model::Asyn, 0, "y", 20, 20)],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(c.full, 2, "both later orders realizable via the A-clause");
    assert_eq!(c.filtered_full, 0);
    assert_eq!(cross_check_reference(&prog), 2);
}

// -- 12. p2p gating: an overtaking message waits behind its channel prefix -----------

#[test]
fn timed_p2p_gating_program() {
    // tid0: m1[50,50]; m2[1,1] on one p2p channel to tid1; tid1: recv(). Under p2p FIFO the
    // single receive reads the channel head m1; its competitor m2 is gated to
    // avail(m2)=max(50,1)=50, exactly touching avail(m1)=50, so the reading is realizable.
    // A bug using avail=arr would see avail(m2)=1 < 50 and wrongly filter it (full=0).
    let prog = SeqProgram::new(vec![
        vec![
            tsend(Model::P2p, 1, "m1", 50, 50),
            tsend(Model::P2p, 1, "m2", 1, 1),
        ],
        vec![recv()],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(
        c.full, 1,
        "reads the channel head m1 (competitor m2 is gated to 50)"
    );
    assert_eq!(c.filtered_full, 0, "p2p gating keeps the reading feasible");
    assert_eq!(cross_check_reference(&prog), 1);
}

// -- 13. asyn is neither gated nor gating, even on a shared (tid,dst) channel ---------

#[test]
fn timed_asyn_not_gated() {
    // tid0: slow[50,50], fast[1,1] (both asyn, same (0,2) channel); tid1: mid[10,10]; tid2:
    // recv()x3. Asyn does not reorder-buffer, so avail = arr and the eager order is
    // fast(1), mid(10), slow(50) — the one realizable full execution. A bug that gated asyn
    // (avail(fast)=max over (0,2)=50) would reorder to mid-first and reject fast,mid,slow.
    let prog = SeqProgram::new(vec![
        vec![
            tsend(Model::Asyn, 2, "slow", 50, 50),
            tsend(Model::Asyn, 2, "fast", 1, 1),
        ],
        vec![tsend(Model::Asyn, 2, "mid", 10, 10)],
        vec![recv(), recv(), recv()],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(c.full, 1, "only fast,mid,slow");
    assert_eq!(c.filtered_full, 5);
    assert_eq!(cross_check_reference(&prog), 1);

    // Direct: the fast,mid,slow reading is feasible on the hand-built graph.
    let mut g = ExecutionGraph::new();
    let slow = g.add_event(0, tsend(Model::Asyn, 2, "slow", 50, 50));
    let fast = g.add_event(0, tsend(Model::Asyn, 2, "fast", 1, 1));
    let mid = g.add_event(1, tsend(Model::Asyn, 2, "mid", 10, 10));
    let r0 = g.add_event(2, recv());
    let r1 = g.add_event(2, recv());
    let r2 = g.add_event(2, recv());
    g.set_rf(r0, Some(fast));
    g.set_rf(r1, Some(mid));
    g.set_rf(r2, Some(slow));
    assert!(
        eager_feasible(&g),
        "fast,mid,slow must be realizable under asyn"
    );
}

// -- 14. a time-infeasible *blocked* terminal is filtered -----------------------------

#[test]
fn timed_filtered_blocked() {
    // T0: a[1,1]->2  ||  T1: b[50,50]->2  ||  T2: recv(); recv(=z).
    // No "z" is ever sent, so T2 always blocks on the second receive: the terminals are the
    // two blocked prefixes r1<-a and r1<-b. r1<-b is infeasible (competitor a is earlier).
    let prog = SeqProgram::new(vec![
        vec![tsend(Model::Asyn, 2, "a", 1, 1)],
        vec![tsend(Model::Asyn, 2, "b", 50, 50)],
        vec![recv(), recv_eq("z")],
    ]);
    let c = timed_counts(&prog);
    assert_eq!(c.full, 0, "recv(=z) can never be satisfied");
    assert_eq!(c.blocked, 1, "r1<-a is a realizable blocked prefix");
    assert_eq!(c.filtered_blocked, 1, "r1<-b is time-infeasible");
    assert_eq!(c.filtered_full, 0);
}

// -- 15. B1 regression: a realizable terminal reachable only via revisit out of an -----
//        infeasible error graph must survive.

#[test]
fn timed_error_revisit_regression() {
    // T0: v=recv(); assert(v != "x")   ||   T1: x[50,50]->0   ||   T2: w[1,1]->0   ||
    // T3: z (untimed) -> 0. The error terminal {recv<-x} is time-infeasible (competitor w
    // is earlier). The realizable full terminal {recv<-z} is reachable only by a backward
    // revisit OUT OF that error graph; because the filter never prunes error subtrees (it
    // only suppresses at record time, and with_time_filter requires collect_errors),
    // {recv<-z} survives.
    fn make() -> System {
        let mut sys = System::new();
        sys.add(|c: Ctx| async move {
            let v = c.recv(|_| true).await;
            c.assert_that(v != "x", "must not read x");
        });
        sys.add(|c: Ctx| async move {
            c.send_within(0, "x", Model::Asyn, Window::new(50, 50));
        });
        sys.add(|c: Ctx| async move {
            c.send_within(0, "w", Model::Asyn, Window::new(1, 1));
        });
        sys.add(|c: Ctx| async move {
            c.send(0, "z", Model::Asyn);
        });
        sys
    }
    let obs = (CountingObserver::new(), ExecutionCollector::new());
    explore(
        make,
        &obs,
        Config::default().collect_errors().with_time_filter(),
    );
    let (cnt, col) = obs;
    assert_eq!(
        cnt.filtered_errors(),
        1,
        "the error terminal reads x and is time-infeasible"
    );
    assert_eq!(col.error_count(), 0, "no surviving error terminal");
    assert_eq!(col.full_count(), 2, "reads w and reads z survive");
    assert!(
        full_reads_value(&col, "z"),
        "the realizable {{recv<-z}} terminal (reached via revisit out of the error graph) \
         must be present"
    );
    assert!(full_reads_value(&col, "w"));
}

// -- 16. invariance: the untimed oracle table is unchanged under the filter -----------

#[test]
fn timed_filter_invariant_on_untimed_oracles() {
    assert_timed_invariant("ssr", &ssr(), &permutations(3), 2, 0);
    assert_timed_invariant("ns_r(3)", &ns_r(3), &permutations(4), 3, 0);
    assert_timed_invariant("ns_nr(3)", &ns_nr(3), &permutations(4), factorial(3), 0);
    assert_timed_invariant("ns_nr_sel(3)", &ns_nr_sel(3), &permutations(4), 1, 0);
    assert_timed_invariant(
        "nworkers(2)",
        &nworkers(2),
        &permutations(4),
        2 * factorial(2),
        0,
    );
    assert_timed_invariant("example_2_8", &example_2_8(), &permutations(2), 1, 0);
    assert_timed_invariant(
        "blocked_no_match",
        &blocked_no_match(),
        &permutations(2),
        0,
        1,
    );
    assert_timed_invariant(
        "blocked_and_full",
        &blocked_and_full(),
        &permutations(3),
        1,
        1,
    );
}

/// The fast path fires before the Asyn/P2p-only model guard, so an all-untimed cd/mbox
/// program passes the filter (no panic) with unchanged counts.
#[test]
fn timed_filter_untimed_cd_mbox_fast_path() {
    let cd = SeqProgram::new(vec![
        vec![send(Model::Cd, 2, "1")],
        vec![send(Model::Cd, 2, "2")],
        vec![recv()],
    ]);
    assert_timed_invariant("cd ssr", &cd, &permutations(3), 2, 0);

    let mbox = SeqProgram::new(vec![
        vec![send(Model::Mbox, 2, "1")],
        vec![send(Model::Mbox, 2, "2")],
        vec![recv()],
    ]);
    assert_timed_invariant("mbox ssr", &mbox, &permutations(3), 2, 0);
}

// -- parallel determinism: the split is identical at threads=1 and threads=4 ----------

#[test]
fn timed_chain_touching_parallel_matches_sequential() {
    let prog = chain_touching();
    let (seq_cnt, seq_col) = run_filtered(&prog, &[0, 1, 2, 3]);

    let par = (CountingObserver::with_shards(4), ExecutionCollector::new());
    explore(
        || prog.clone(),
        &par,
        Config::default()
            .collect_errors()
            .with_time_filter()
            .with_threads(4),
    );
    let (par_cnt, par_col) = par;

    assert_eq!(
        par_col.full_count(),
        seq_col.full_count(),
        "full under 4 threads"
    );
    assert_eq!(
        par_cnt.filtered(),
        seq_cnt.filtered(),
        "filtered under 4 threads"
    );
    assert_eq!(par_col.full_count(), 3);
    assert_eq!(par_cnt.filtered(), 3);
    let seq_keys: BTreeSet<String> = seq_col.full_keys().into_iter().collect();
    let par_keys: BTreeSet<String> = par_col.full_keys().into_iter().collect();
    assert_eq!(seq_keys, par_keys, "full key-set under 4 threads");
}
