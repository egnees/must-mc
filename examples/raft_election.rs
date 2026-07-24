//! # Raft-style leader election as a `must` model (bounded)
//!
//! A leader election written the way a real Raft node is: an event loop with explicit
//! persistent vs volatile state and roles that emerge from the protocol. A follower becomes
//! a candidate when its election timer expires (a missed heartbeat); a candidate becomes
//! leader when it wins a majority; any node steps down when it sees a higher term. The
//! process code does not know it is inside a model checker. The only model-specific thing is
//! a `nondet` fault-injection point (crash / recover).
//!
//! Run it (note the `--` before the example's own flags):
//! `cargo run --release --example raft_election -- [-n N] [--terms T] [--ticks K] [--faults F] [--bug] [--threads W]`
//! Defaults: `-n 3 --terms 2 --ticks 4 --faults 1` (bug off), `--threads` = performance cores.
//!
//! ## Running in parallel
//!
//! The search runs on `explore` with `Config::threads` set: subtrees are independent, so
//! `W` worker threads explore them at once. Each worker builds its own cluster (the runtime
//! is not `Send`) while `Send` execution graphs flow through a shared work queue. Counts
//! come from a shared `CountingObserver` whose per-worker shards keep the tallies
//! contention-free. The binary uses `mimalloc` as its allocator (a dev-dependency, so the
//! library stays dependency-free).
//!
//! ### Huge pages (Linux)
//!
//! On Linux the binary asks mimalloc for large OS pages (2 MiB) at startup, best-effort. For
//! that to take hold the kernel's transparent-huge-page policy must allow it (`madvise` or
//! `always`), or you can reserve explicit hugetlb pages and point mimalloc at them via its
//! env vars (`MIMALLOC_LARGE_OS_PAGES`, `MIMALLOC_RESERVE_HUGE_OS_PAGES`). A no-op on macOS.
//!
//! ## Crash and recovery (state persistence)
//!
//! A crash loses volatile state (`role` reverts to Follower on restart) but keeps persistent
//! state (`current_term`, `voted_for`), exactly Raft's on-disk state. Two fault points are
//! injected (both `nondet`), each a safety-relevant moment:
//!   * a fresh leader may crash before it can lead, so its followers' timers expire and they
//!     re-elect (the run does not stop at the first leader);
//!   * a follower may crash right after voting: with correct persistence it still remembers
//!     its vote, but the `Bug::LoseVote` variant forgets it and votes again in the same term,
//!     electing two leaders, which the monitor catches. Persistence is thus a checked safety
//!     mechanism, not decoration.
//!
//! ## What the model can and cannot express
//!
//! Expressible: the role state machine (ordinary control flow), election and heartbeat
//! timers (a `recv_timeout` that times out is the timer firing), term-based step-down, crash
//! and recover with persisted state, and the election-safety monitor.
//!
//! Not expressible: unbounded execution. Stateless DPOR enumerates the finite set of
//! consistent execution graphs, and a forever-running protocol has infinitely many. So each
//! node runs a bounded number of event-loop ticks and terms, and crashes are bounded. Within
//! the bound the full elect -> crash -> re-elect cycle is modelled and verified. There is no
//! real time: timers are nondeterministic timeouts, so DPOR explores every timeout pattern (a
//! superset of any real clock), which is safety-sound; liveness is not checked (Must is
//! safety-only). Everything is p2p, and receives are selective (each waits for a specific
//! message) so `rf` stays deterministic and the state space tractable.

use std::collections::BTreeMap;

use clap::Parser;
use must::event::Model;
use must::{explore, Config, CountingObserver, Ctx, System};

// A dev-dependency, so only the example binary uses it; the library stays dependency-free.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Ask mimalloc to back allocations with large OS pages (2 MiB). Best-effort: mimalloc falls
/// back to 4 KiB pages if the OS has none (see the module docs for enabling them). A no-op
/// off Linux.
fn enable_hugepages() {
    if cfg!(target_os = "linux") {
        // SAFETY: a single FFI call into mimalloc's thread-safe option API, made once at
        // startup before any heavy allocation. mimalloc re-checks `mi_option_large_os_pages`
        // on each later OS allocation, so setting it here covers the whole run.
        unsafe {
            libmimalloc_sys::mi_option_set_enabled(libmimalloc_sys::mi_option_large_os_pages, true);
        }
    }
}

/// Volatile role: reset to `Follower` on every (re)start.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    Follower,
    Candidate,
    Leader,
}

/// The state Raft keeps on stable storage; it MUST survive a crash for safety.
#[derive(Clone, Copy)]
struct Persistent {
    current_term: u64,
    voted_for: Option<usize>, // vote for `current_term`; cleared when the term advances
}

/// Injected safety bug.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Bug {
    /// Correct: `voted_for` is persisted across a crash.
    None,
    /// Bug: a crash loses `voted_for`, so a recovered node may vote a second time in a term
    /// it already voted in, electing two leaders.
    LoseVote,
}

/// The two inbound RPCs a waiting node reacts to (vote replies are collected separately).
enum In {
    RequestVote { term: u64, cand: usize },
    Heartbeat { term: u64 },
}

fn rv(term: u64, cand: usize) -> String {
    format!("RV:{term}:{cand}")
}
fn vote(term: u64, voter: usize, cand: usize) -> String {
    format!("VOTE:{term}:{voter}:{cand}")
}
fn hb(term: u64, leader: usize) -> String {
    format!("HB:{term}:{leader}")
}

fn parse_in(s: &str) -> Option<In> {
    let f: Vec<&str> = s.split(':').collect();
    match f.as_slice() {
        ["RV", t, c] => Some(In::RequestVote {
            term: t.parse().ok()?,
            cand: c.parse().ok()?,
        }),
        ["HB", t, _leader] => Some(In::Heartbeat {
            term: t.parse().ok()?,
        }),
        _ => None,
    }
}

/// Raft majority over the fixed cluster size: what guarantees at most one leader per term.
fn majority(n: usize) -> usize {
    n / 2 + 1
}

/// Adopt a newer term seen in an RPC (and, per Raft, forget the vote). Returns whether we
/// saw a strictly newer term.
fn observe_term(p: &mut Persistent, term: u64) -> bool {
    if term > p.current_term {
        p.current_term = term;
        p.voted_for = None;
        true
    } else {
        false
    }
}

/// May we grant our (single) vote for `current_term` to `cand`? (No log, so always up to date.)
fn can_vote(p: &Persistent, cand: usize) -> bool {
    p.voted_for.is_none() || p.voted_for == Some(cand)
}

/// A modelled crash: has one happened? Consumes the per-node fault budget and returns true.
async fn crashes_now(c: &Ctx, budget: &mut u32) -> bool {
    if *budget == 0 {
        return false;
    }
    // min(S) = "alive" is the canonical (no-fault) value; "crashed" is a modelled failure.
    if c.nondet(["alive", "crashed"]).await == "crashed" {
        *budget -= 1;
        true
    } else {
        false
    }
}

/// Wait for the next heartbeat or vote request; `None` means the election timer fired first.
async fn wait_rpc(c: &Ctx) -> Option<In> {
    c.recv_timeout(|x: &str| x.starts_with("HB:") || x.starts_with("RV:"))
        .await
        .and_then(|s| parse_in(&s))
}

/// Follower tick: a heartbeat keeps us following (timer resets); a vote request may earn our
/// vote (after which a crash may be injected, the persistence-critical moment); a timeout is
/// the election timer expiring, so we become a candidate.
async fn follower_tick(c: &Ctx, k: usize, p: &mut Persistent, faults: &mut u32, bug: Bug) -> Role {
    match wait_rpc(c).await {
        None => Role::Candidate,
        Some(In::Heartbeat { term }) => {
            observe_term(p, term);
            Role::Follower
        }
        Some(In::RequestVote { term, cand }) => {
            if term >= p.current_term {
                observe_term(p, term);
                if can_vote(p, cand) {
                    p.voted_for = Some(cand);
                    c.send(cand, vote(p.current_term, k, cand), Model::P2p);
                    // Crash right after voting. This only matters under the bug: correct
                    // persistence keeps `voted_for`, making the crash an observably-identical
                    // no-op, so we only inject it where it can change the outcome.
                    if bug == Bug::LoseVote && crashes_now(c, faults).await {
                        p.voted_for = None; // BUG: the vote was never persisted
                    }
                }
            }
            Role::Follower
        }
    }
}

/// Candidate tick: bump the term, vote for self, request votes, tally replies (one selective
/// receive per peer). A majority means leader (announce), but the fresh leader may crash
/// immediately, which is what triggers a re-election.
async fn candidate_tick(
    c: &Ctx,
    k: usize,
    n: usize,
    max_term: u64,
    p: &mut Persistent,
    faults: &mut u32,
) -> Role {
    if p.current_term + 1 > max_term {
        return Role::Follower; // bound: no elections past the term cap
    }
    p.current_term += 1;
    p.voted_for = Some(k);
    let t = p.current_term;
    for j in 0..n {
        if j != k {
            c.send(j, rv(t, k), Model::P2p);
        }
    }
    let mut votes = 1; // self
    for j in 0..n {
        if j != k {
            let want = vote(t, j, k);
            if c.recv_timeout(move |x: &str| x == want).await.is_some() {
                votes += 1;
            }
        }
    }
    if votes >= majority(n) {
        c.send(n, format!("LEADER:{t}:{k}"), Model::P2p);
        if crashes_now(c, faults).await {
            return Role::Follower;
        }
        Role::Leader
    } else {
        Role::Follower
    }
}

/// Leader tick: broadcast a heartbeat, then wait one interval; step down on any higher term.
async fn leader_tick(c: &Ctx, k: usize, n: usize, p: &mut Persistent) -> Role {
    for j in 0..n {
        if j != k {
            c.send(j, hb(p.current_term, k), Model::P2p);
        }
    }
    match wait_rpc(c).await {
        None => Role::Leader, // heartbeat interval elapsed -> heartbeat again
        Some(In::Heartbeat { term }) => {
            if observe_term(p, term) {
                Role::Follower
            } else {
                Role::Leader
            }
        }
        Some(In::RequestVote { term, cand }) => {
            if term > p.current_term {
                observe_term(p, term);
                if can_vote(p, cand) {
                    p.voted_for = Some(cand);
                    c.send(cand, vote(p.current_term, k, cand), Model::P2p);
                }
                Role::Follower
            } else {
                Role::Leader
            }
        }
    }
}

/// Build the cluster: `n` Raft nodes (tids `0..n`) plus the election-safety monitor (tid
/// `n`). Each node runs at most `ticks` event-loop iterations and may crash up to `faults`
/// times (its per-node crash budget, which keeps the fault space finite).
fn raft_cluster(n: usize, max_term: u64, ticks: usize, faults: u32, bug: Bug) -> System {
    let mut sys = System::new();

    for _ in 0..n {
        sys.add(move |c: Ctx| async move {
            let k = c.tid();
            let mut p = Persistent {
                current_term: 0,
                voted_for: None,
            };
            let mut role = Role::Follower;
            let mut faults = faults; // per-node crash budget, spent as crashes occur

            for _ in 0..ticks {
                if p.current_term > max_term {
                    break;
                }
                role = match role {
                    Role::Follower => follower_tick(&c, k, &mut p, &mut faults, bug).await,
                    Role::Candidate => {
                        candidate_tick(&c, k, n, max_term, &mut p, &mut faults).await
                    }
                    Role::Leader => leader_tick(&c, k, n, &mut p).await,
                };
            }
        });
    }

    // Monitor (tid n): election safety, at most one leader per term. Selective per (term,
    // node) receives keep `rf` deterministic; each node announces a given term at most once.
    sys.add(move |c: Ctx| async move {
        let mut per_term: BTreeMap<u64, usize> = BTreeMap::new();
        for t in 1..=max_term {
            for k in 0..n {
                let want = format!("LEADER:{t}:{k}");
                if c.recv_timeout(move |x: &str| x == want).await.is_some() {
                    *per_term.entry(t).or_insert(0) += 1;
                }
            }
        }
        for (_t, count) in per_term {
            c.assert_that(
                count == 1,
                "election safety violated: two leaders in one term",
            );
        }
    });

    sys
}

/// Bounded Raft-style leader election, model-checked by `must` (safety only). The state
/// space grows fast with --ticks, --terms, and --faults.
#[derive(Parser)]
struct Args {
    /// Number of cluster nodes.
    #[arg(short = 'n', long = "nodes", default_value_t = 3)]
    n: usize,
    /// Term cap: the bound that keeps the state space finite.
    #[arg(long, default_value_t = 2)]
    terms: u64,
    /// Event-loop ticks per node (the main state-space knob).
    #[arg(long, default_value_t = 4)]
    ticks: usize,
    /// Per-node crash budget (0 disables crashes and crash-driven re-election).
    #[arg(long, default_value_t = 1)]
    faults: u32,
    /// Inject the non-persistent-`voted_for` bug (Election Safety must then break).
    #[arg(long, default_value_t = false)]
    bug: bool,
    /// Worker threads for the parallel explorer (default: all available cores).
    #[arg(long, default_value_t = 0)]
    threads: usize,
}

fn main() {
    enable_hugepages();

    let Args {
        n,
        terms,
        ticks,
        faults,
        bug,
        threads,
    } = Args::parse();
    let kind = if bug { Bug::LoseVote } else { Bug::None };
    let threads = if threads == 0 {
        std::thread::available_parallelism().map_or(1, |t| t.get())
    } else {
        threads
    };

    println!(
        "Raft-style leader election — n={n}, terms={terms}, ticks={ticks}, faults={faults}, \
         bug={}, threads={threads}  (p2p, safety-only)\n",
        if bug { "on (LoseVote)" } else { "off" }
    );

    let cfg = Config::default().collect_errors().with_threads(threads);

    let counts = CountingObserver::with_shards(threads);

    explore(
        move || raft_cluster(n, terms, ticks, faults, kind),
        &counts,
        cfg,
    );

    println!(
        "  {} executions — {} full, {} blocked, {} safety violations",
        counts.full() + counts.blocked() + counts.errors(),
        counts.full(),
        counts.blocked(),
        counts.errors(),
    );
}
