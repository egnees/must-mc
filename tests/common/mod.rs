//! Shared oracle helpers. Lives under `tests/common/` so it is *not* compiled as its own
//! test binary; each oracle file pulls it in with `mod common;`.
//!
//! The paper's benchmarks are all straight-line, value-independent programs, so a tiny
//! table-driven [`SeqProgram`] is the right vehicle: `next` advances purely by trace
//! length, no coroutine replay, so the large counters (ns+nr(8)=40320, ...) stay fast.
//! A handful of oracles are *also* built on the real `System` runtime (in the oracle
//! files themselves) to prove the runtime -> explorer path yields the same numbers.

// Each oracle crate uses a different subset of these helpers, so unused items are
// expected per-crate; silence the resulting dead-code warnings for the shared module.
#![allow(dead_code)]

use std::collections::BTreeSet;

use must::event::{Label, Model, Pred};
use must::{explore, Config, ExecutionCollector, Program, System, ThreadNext, Val};

/// A straight-line (value-independent) program: `threads[i]` is thread `i`'s ordered
/// event list. `next(traces)[i]` is the `(len+1)`-th event of thread `i`, where `len`
/// is how many of its events are already committed (`traces[i].len()`). Since control
/// flow never branches on received values, this needs no replay.
#[derive(Clone)]
pub struct SeqProgram {
    pub threads: Vec<Vec<Label>>,
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

impl SeqProgram {
    pub fn new(threads: Vec<Vec<Label>>) -> Self {
        SeqProgram { threads }
    }
}

// -- Label builders ---------------------------------------------------------------

pub fn send(model: Model, dst: usize, v: &str) -> Label {
    Label::send(model, dst, v)
}
/// Non-selective blocking receive (`recv(true)`).
pub fn recv() -> Label {
    Label::recv(Pred::any())
}
/// Selective blocking receive (`recv(|x| x == v)`).
pub fn recv_eq(v: &str) -> Label {
    Label::recv(Pred::eq(v))
}
/// Non-selective non-blocking receive (`recv_timeout(true)`) -- may read no message.
pub fn recv_nb() -> Label {
    Label::recv_nb(Pred::any())
}
/// Selective non-blocking receive (`recv_timeout(|x| x == v)`).
pub fn recv_nb_eq(v: &str) -> Label {
    Label::recv_nb(Pred::eq(v))
}
/// Data-nondeterminism `ND^S` over the option set `vals` (Algorithm 1 lines 6/19).
pub fn nondet(vals: &[&str]) -> Label {
    Label::nondet(vals.iter().copied())
}

// -- Combinatorics ----------------------------------------------------------------

pub fn factorial(n: usize) -> usize {
    (1..=n).product()
}

/// Every permutation of `0..n`. Only call for small `n` (`n!` grows fast); use
/// [`sample_perms`] for larger thread counts.
pub fn permutations(n: usize) -> Vec<Vec<usize>> {
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

/// A small, representative set of priority permutations for thread counts where
/// enumerating all `n!` would be wasteful: identity, reverse, and a rotation. Enough to
/// spot-check that execution counts and terminal-key sets are priority-invariant.
pub fn sample_perms(n: usize) -> Vec<Vec<usize>> {
    let id: Vec<usize> = (0..n).collect();
    let rev: Vec<usize> = (0..n).rev().collect();
    let mut rot: Vec<usize> = (1..n).collect();
    rot.push(0);
    let mut out = vec![id];
    if !out.contains(&rev) {
        out.push(rev);
    }
    if !out.contains(&rot) {
        out.push(rot);
    }
    out
}

// -- Running & assertions ---------------------------------------------------------

/// Run `prog` under an explicit priority permutation, collecting the terminal executions.
pub fn run(prog: &SeqProgram, perm: &[usize]) -> ExecutionCollector {
    let col = ExecutionCollector::new();
    explore(
        || prog.clone(),
        &col,
        Config::default().with_priorities(perm.to_vec()),
    );
    col
}

/// No two terminal (full or blocked) executions share a canonical `(E, po, rf)` key --
/// the universal Theorem 4.1 "no duplicates" assertion.
pub fn assert_no_duplicates(col: &ExecutionCollector, ctx: &str) {
    let keys = col.terminal_keys();
    let unique: BTreeSet<&String> = keys.iter().collect();
    assert_eq!(
        keys.len(),
        unique.len(),
        "{ctx}: duplicate canonical keys among terminal executions:\n{keys:#?}"
    );
}

/// Core oracle assertion. For every permutation in `perms`, run `prog` and require:
///   * `full_count == full`, `blocked_count == blocked`, `error_count == 0`;
///   * no duplicate terminal executions;
///   * the *set* of terminal canonical keys is identical across permutations
///     (execution equivalence classes are priority-independent -- completeness +
///     optimality of Must).
pub fn assert_oracle(
    name: &str,
    prog: &SeqProgram,
    perms: &[Vec<usize>],
    full: usize,
    blocked: usize,
) {
    let mut reference: Option<BTreeSet<String>> = None;
    for perm in perms {
        let col = run(prog, perm);
        assert_eq!(
            col.full_count(),
            full,
            "{name} under priorities {perm:?}: full_count"
        );
        assert_eq!(
            col.blocked_count(),
            blocked,
            "{name} under priorities {perm:?}: blocked_count"
        );
        assert_eq!(
            col.error_count(),
            0,
            "{name} under priorities {perm:?}: error_count"
        );
        assert_no_duplicates(&col, name);

        let keyset: BTreeSet<String> = col.terminal_keys().into_iter().collect();
        match &reference {
            None => reference = Some(keyset),
            Some(r) => assert_eq!(
                &keyset, r,
                "{name}: terminal key set differs under priorities {perm:?} \
                 (executions must be priority-invariant)"
            ),
        }
    }
}

/// Convenience: assert an oracle under the default `0..N` priorities only (for large
/// benchmarks where sweeping permutations is unnecessary).
pub fn assert_oracle_default(name: &str, prog: &SeqProgram, full: usize, blocked: usize) {
    let n = prog.num_threads();
    let id: Vec<usize> = (0..n).collect();
    assert_oracle(name, prog, &[id], full, blocked);
}

// -- Runtime (coroutine) oracle helpers -------------------------------------------

/// Run a coroutine `System` under a representative set of priority permutations of its
/// `n` threads and assert the two invariants that must hold for *any* correct Must run,
/// regardless of a hand-derived count:
///   * **no duplicates** -- distinct canonical `(E, po, rf)` keys over full-or-blocked
///     terminals;
///   * **priority invariance** -- the terminal-key set and the `(full, blocked)` counts
///     are identical across permutations (completeness + optimality).
///
/// Also asserts `error_count == 0` (the correct-protocol case; broken variants go through
/// [`assert_monitor_bites`] instead). Returns the invariant `(full, blocked)`.
///
/// All permutations for `n <= 4`; a representative sample ([`sample_perms`]) beyond that.
/// `make` builds a fresh system per run (the runtime is not shareable across threads).
pub fn assert_system_invariant(
    make: impl Fn() -> System + Sync,
    n: usize,
    name: &str,
) -> (usize, usize) {
    let perms = if n <= 4 {
        permutations(n)
    } else {
        sample_perms(n)
    };
    let mut reference: Option<BTreeSet<String>> = None;
    let mut counts = (0, 0);
    for perm in &perms {
        let col = ExecutionCollector::new();
        explore(&make, &col, Config::default().with_priorities(perm.clone()));
        assert_eq!(
            col.error_count(),
            0,
            "{name} under priorities {perm:?}: unexpected safety violation (error_count)"
        );
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
                "{name}: terminal key set differs under priorities {perm:?} \
                 (executions must be priority-invariant)"
            ),
        }
    }
    counts
}

/// Whether some collected terminal execution has a receive reading no message -- the
/// witness that a crash (a `recv_timeout` timing out on a lost or slow message) is
/// genuinely exercised.
pub fn any_bottom_read(col: &ExecutionCollector) -> bool {
    col.terminals().iter().any(|e| {
        let g = e.graph();
        g.recvs().into_iter().any(|r| g.reads_bottom(r))
    })
}

/// Negative safety oracle: a deliberately broken protocol variant must make its monitor
/// bite. Runs with [`Config::collect_errors`] (so *every* violating execution surfaces as
/// its own `Error` terminal rather than aborting the whole search at the first one), under
/// a representative sweep of the `n`-thread priority permutations, and asserts on *each*:
///   * `error_count > 0` -- the monitor caught at least one violation;
///   * `blocked_count == 0`;
///   * `full_count + error_count == base` -- the broken variant has the *same* executions
///     as the correct one (`base`), only reclassified: a violation turns a would-be full
///     execution into an error terminal (a second, independent check on `base`);
///   * the `(full, error)` split and the full-or-blocked key-set are **priority-invariant**
///     (so the classification is schedule-independent, matching the positive oracles).
///
/// Returns the invariant `(full, error)` split so callers can assert the exact numbers.
/// `make` builds a fresh system per run (the runtime is not shareable across threads).
pub fn assert_monitor_bites(
    make: impl Fn() -> System + Sync,
    n: usize,
    base: usize,
    name: &str,
) -> (usize, usize) {
    let perms = if n <= 4 {
        permutations(n)
    } else {
        sample_perms(n)
    };
    let mut reference: Option<(BTreeSet<String>, usize, usize)> = None;
    for perm in &perms {
        let col = ExecutionCollector::new();
        explore(
            &make,
            &col,
            Config::default()
                .with_priorities(perm.clone())
                .collect_errors(),
        );
        assert!(
            col.error_count() > 0,
            "{name} under priorities {perm:?}: expected the monitor to catch a violation"
        );
        assert_eq!(
            col.blocked_count(),
            0,
            "{name} under priorities {perm:?}: unexpected blocked executions"
        );
        assert_eq!(
            col.full_count() + col.error_count(),
            base,
            "{name} under priorities {perm:?}: full ({}) + error ({}) != base {base}",
            col.full_count(),
            col.error_count()
        );
        let keys = col.terminal_keys();
        let set: BTreeSet<String> = keys.iter().cloned().collect();
        assert_eq!(
            keys.len(),
            set.len(),
            "{name} under priorities {perm:?}: duplicate terminal keys"
        );
        let split = (col.full_count(), col.error_count());
        match &reference {
            None => reference = Some((set, split.0, split.1)),
            Some((rset, rf, re)) => {
                assert_eq!(&set, rset, "{name}: terminal set differs under {perm:?}");
                assert_eq!(
                    split,
                    (*rf, *re),
                    "{name}: (full,error) differs under {perm:?}"
                );
            }
        }
    }
    let (_, full, error) = reference.expect("at least one permutation");
    (full, error)
}

// -- Two-phase commit (2PC) model -------------------------------------------------

/// Which (if any) safety bug a [`twopc_system`] coordinator has.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TwoPcBug {
    /// Correct: COMMIT iff every participant voted YES; a timed-out vote (no message) =>
    /// ABORT.
    None,
    /// Atomicity bug: commit regardless of the votes.
    IgnoreVotes,
    /// Atomicity bug: treat a timed-out vote (no message) as a YES (commit unless an
    /// *explicit* NO was seen).
    TimeoutMeansYes,
    /// Agreement bug: the global decision (and `DN`) is ABORT, but participant 1 is told to
    /// COMMIT -- so the participants adopt *different* decisions. Isolates the monitor's
    /// **agreement** assert: atomicity cannot fire (no global commit), so only the
    /// disagreement is caught.
    DivergentDecision,
}

/// Build a two-phase-commit `System`: coordinator `= tid 0`, participants `= 1..=n`, and
/// (when `monitored`) an atomicity/agreement monitor `Tm = tid n+1`. Protocol messages
/// use `model`; **all monitor notifications use `Model::Cd`**. When `crash`, the
/// coordinator collects votes with `recv_timeout`, so a lost or slow vote reads no message
/// (a suspected -- possibly false -- failure). Every participant always runs to
/// completion; a "crash" is only what the coordinator *observes*.
pub fn twopc_system(n: usize, model: Model, crash: bool, monitored: bool, bug: TwoPcBug) -> System {
    let mut sys = System::new();
    let tm = n + 1;

    // coordinator = tid 0
    sys.add(move |c| async move {
        for p in 1..=n {
            c.send(p, "PREP", model); // msg 1: PREPARE
        }
        let mut votes: Vec<Option<String>> = Vec::with_capacity(n);
        for p in 1..=n {
            let prefix = format!("V:{p}:");
            let v = if crash {
                c.recv_timeout(move |x: &str| x.starts_with(&prefix)).await
            } else {
                Some(c.recv(move |x: &str| x.starts_with(&prefix)).await)
            };
            votes.push(v); // msg 2: VOTE (None = suspected crash)
        }
        let decision = match bug {
            TwoPcBug::IgnoreVotes => "COMMIT",
            TwoPcBug::TimeoutMeansYes => {
                // A timeout (no message) treated as YES: abort only on an explicit NO.
                if votes
                    .iter()
                    .any(|v| v.as_deref().is_some_and(|s| s.ends_with("NO")))
                {
                    "ABORT"
                } else {
                    "COMMIT"
                }
            }
            // The global decision is ABORT; the per-participant divergence is applied at
            // broadcast time below.
            TwoPcBug::DivergentDecision => "ABORT",
            TwoPcBug::None => {
                // Correct: all-YES => COMMIT, else (incl. any timeout) => ABORT.
                if votes
                    .iter()
                    .all(|v| v.as_deref().is_some_and(|s| s.ends_with("YES")))
                {
                    "COMMIT"
                } else {
                    "ABORT"
                }
            }
        };
        if monitored {
            c.send(tm, format!("DN:{decision}"), Model::Cd); // msg 3n: BEFORE broadcast
        }
        for p in 1..=n {
            // DivergentDecision tells participant 1 to COMMIT while the global (DN) is
            // ABORT -- the participants adopt different decisions (agreement violation).
            let d_p = if bug == TwoPcBug::DivergentDecision && p == 1 {
                "COMMIT"
            } else {
                decision
            };
            c.send(p, format!("D:{d_p}"), model); // msg 3: DECISION
        }
    });

    // participants = tids 1..=n
    for p in 1..=n {
        sys.add(move |c| async move {
            let _ = c.recv(|x: &str| x == "PREP").await; // msg 1
            let vote = c.nondet(["NO", "YES"]).await; // ND^S: min(S)="NO" first
            if monitored {
                c.send(tm, format!("VN:{p}:{vote}"), Model::Cd); // msg 2n: BEFORE the vote send
            }
            c.send(0, format!("V:{p}:{vote}"), model); // msg 2
            let d = c.recv(|x: &str| x.starts_with("D:")).await; // msg 3
            if monitored {
                let dec = d.strip_prefix("D:").unwrap_or(&d).to_string();
                c.send(tm, format!("AN:{p}:{dec}"), Model::Cd); // msg 4n: AFTER the decision recv
            }
        });
    }

    // monitor = tid n+1
    if monitored {
        sys.add(move |c| async move {
            let mut vn: Vec<String> = Vec::with_capacity(n);
            for p in 1..=n {
                let prefix = format!("VN:{p}:");
                vn.push(c.recv(move |x: &str| x.starts_with(&prefix)).await);
            }
            let dn = c.recv(|x: &str| x.starts_with("DN:")).await;
            let mut an: Vec<String> = Vec::with_capacity(n);
            for p in 1..=n {
                let prefix = format!("AN:{p}:");
                an.push(c.recv(move |x: &str| x.starts_with(&prefix)).await);
            }
            let commit = dn == "DN:COMMIT";
            // Atomicity/validity: a global COMMIT requires every true vote to be YES.
            let all_yes = vn.iter().all(|v| v.ends_with("YES"));
            c.assert_that(!commit || all_yes, "atomicity: COMMIT requires all YES");
            // Agreement: every participant adopted the single global decision.
            let global = dn.strip_prefix("DN:").unwrap_or(&dn);
            for a in &an {
                let dec = a.rsplit(':').next().unwrap_or("");
                c.assert_that(
                    dec == global,
                    "agreement: participant adopted the global decision",
                );
            }
        });
    }

    sys
}

// -- Leader election model --------------------------------------------------------

/// Which (if any) tie-break bug a [`leader_system`] node has.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LeaderBug {
    /// Correct: ties broken by lowest tid (a deterministic function of the ballot view).
    None,
    /// Bug: a node breaks ties in its *own* favour, so two tied nodes disagree.
    SelfishTieBreak,
}

/// The elected leader given a node's `view` of `(ballot, tid)` (highest ballot wins).
/// Correct tie-break is lowest tid; [`LeaderBug::SelfishTieBreak`] prefers `me` when `me`
/// is tied for the maximum.
fn leader_winner(view: &[Option<(u32, usize)>], me: usize, bug: LeaderBug) -> usize {
    let max_b = view.iter().flatten().map(|&(b, _)| b).max().unwrap_or(0);
    let tied: Vec<usize> = view
        .iter()
        .flatten()
        .filter(|&&(b, _)| b == max_b)
        .map(|&(_, tid)| tid)
        .collect();
    match bug {
        LeaderBug::None => *tied.iter().min().unwrap(),
        LeaderBug::SelfishTieBreak => {
            if tied.contains(&me) {
                me
            } else {
                *tied.iter().min().unwrap()
            }
        }
    }
}

/// Build a leader-election `System`: `n` nodes `0..n`, and (when `monitored`) a uniqueness
/// monitor `Tm = tid n`. Each node's ballot is the sum of `incr` nondet increments from
/// `{1,2,3}` (`leader(n, incr)`); it broadcasts its ballot to every peer, collects theirs
/// (with `recv_timeout` when `crash`, so a lost ballot reads no message => no quorum), and
/// elects the highest ballot (ties by lowest tid, unless `bug`). Monitored nodes
/// **always** announce their elected leader under `Model::Cd` -- even without a quorum
/// (the *naive* protocol), which is what exposes split-brain under crashes.
pub fn leader_system(
    n: usize,
    incr: usize,
    model: Model,
    crash: bool,
    monitored: bool,
    bug: LeaderBug,
) -> System {
    let mut sys = System::new();
    let tm = n;

    for k in 0..n {
        sys.add(move |c| async move {
            let mut ballot: u32 = 0;
            for _ in 0..incr {
                let v = c.nondet(["1", "2", "3"]).await;
                ballot += v.parse::<u32>().unwrap_or(0);
            }
            for j in 0..n {
                if j != k {
                    c.send(j, format!("B:{k}:{ballot}"), model); // broadcast ballot
                }
            }
            let mut view: Vec<Option<(u32, usize)>> = vec![None; n];
            // `j` is the peer's tid: it names both the selective predicate `"B:{j}:"` and
            // the `view` slot, so a bare iterator would lose the intent.
            #[allow(clippy::needless_range_loop)]
            for j in 0..n {
                if j == k {
                    view[k] = Some((ballot, k));
                    continue;
                }
                let prefix = format!("B:{j}:");
                let r = if crash {
                    c.recv_timeout(move |x: &str| x.starts_with(&prefix)).await
                } else {
                    Some(c.recv(move |x: &str| x.starts_with(&prefix)).await)
                };
                // r == None: peer j's ballot timed out -- no quorum, but the naive
                // protocol still announces below.
                let b = match r {
                    Some(msg) => msg
                        .rsplit(':')
                        .next()
                        .and_then(|s| s.parse::<u32>().ok())
                        .unwrap_or(0),
                    None => continue,
                };
                view[j] = Some((b, j));
            }
            let winner = leader_winner(&view, k, bug);
            if monitored {
                c.send(tm, format!("A:{k}:{winner}"), Model::Cd);
            }
        });
    }

    if monitored {
        sys.add(move |c| async move {
            let mut ann: Vec<String> = Vec::with_capacity(n);
            for k in 0..n {
                let prefix = format!("A:{k}:");
                ann.push(c.recv(move |x: &str| x.starts_with(&prefix)).await);
            }
            let w0 = ann[0].rsplit(':').next().unwrap_or("").to_string();
            for a in &ann[1..] {
                let w = a.rsplit(':').next().unwrap_or("");
                c.assert_that(w == w0, "uniqueness: nodes disagree on the leader");
            }
        });
    }

    sys
}
