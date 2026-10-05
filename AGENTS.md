# AGENTS.md

This file provides guidance to Codex (Codex.ai/code) when working with code in this repository.

## What this is

`must` is a from-scratch Rust implementation of the **Must** optimal DPOR for
message-passing concurrency (Enea et al., *Model Checking Distributed Protocols in
Must*, OOPSLA 2024). It model-checks distributed protocols by exploring every
consistent execution graph exactly once. The correctness bar is concrete: the number
of executions it reports on the paper's benchmarks must equal the paper's Tables 1–3.

The end goal (not yet built) is to extend the model with **time intervals** on message
delivery and receive timeouts — see "Planned extension" below.

### Authoritative references (read before non-trivial work)

The paper is not in this repo; two documents in the parent directory reconstruct it in
full and are the source of truth for every algorithmic decision:

- `../must_konspekt.md` — the paper distilled: **Algorithm 1 verbatim (§4.2, lines
  1–22)**, its line-by-line reading (§4.3–4.9), the correctness invariants (§9.2), the
  **26 typical implementation errors (§9.4)**, and the oracle counts (§8, §9.3). Cite it
  as `§N` / `line N` — the code comments already do.
- `PLAN.md` (in this repo) — the implementation plan, **validated by the `must-expert`
  agent**; §13 records six resolved design questions (O1–O6) whose answers are baked in.

When something in the code looks like a deviation from the paper, check PLAN §3/§5/§9 and
§13 first — the intentional deviations are documented there, not invented.

## Commands

```bash
cargo test                        # full suite (fast tests only)
cargo test --release              # same, optimized — run before trusting perf claims
cargo test -- --ignored           # the 4 heavy oracles (see below); ~10s
cargo test --release -- --ignored # heavy oracles, fast
cargo test --test oracles         # one test binary (oracles / models / fuzz / explorer / ...)
cargo test <name>                 # one test by (substring of) name, e.g. `cargo test nnr`
cargo clippy --all-targets -- -D warnings   # must stay clean; CI-equivalent gate
```

Zero external dependencies is a hard invariant — do not add crates (std-only, including
the hand-driven futures in `runtime`). Heavy `#[ignore]`d oracles: `nsnr_8` (=40320),
`nworkers_6`, `nworkers_7` (=10080), `fuzz_large_corpus` (800 programs).

## Architecture

The pipeline is a one-directional dependency chain; each stage is independently testable
and most tests target a single stage with hand-built inputs.

```
runtime (coroutines) ──impl──▶ Program trait ──▶ scheduler (next_P) ──▶ explorer (Algorithm 1)
                                                                              │
                                    graph + consistency ◀──uses── revisit ────┤
                                                                              ▼
                                                              observer + render
```

- **`event`** — `Label` (`Send{model,dst,val}` / `Recv{pred,blocking}` / `Error`),
  `EventId{tid,idx}` whose `Ord` is lexicographic `(tid,idx)` (this *is* the tiebreaker
  order), `Pred` (selective-receive predicate). No `Nondet` variant yet.
- **`graph`** — `ExecutionGraph` = ⟨E, po, rf⟩ + insertion order `≤_G` (stamps). **No co,
  no init event, no RMW.** `po` is the per-thread vector order; `rf(r)` is
  `Option<EventId>` where `None` = ⊥. `restrict` re-stamps survivors (GenMC `cutToStamp`)
  and requires a po-prefix-closed keep set. `canonical_key` is the stamp-independent dedup
  key.
- **`consistency`** — `consistent(g)` = well-formedness + `consistent_M` for each model
  used. asyn = well-formed only; p2p/cd use so-formulas (mind `;` binds tighter than `∩`);
  **mbox is a global acyclicity check** over an A∪B∪C edge graph (Di Giusto POPL 2023
  Def 4.2), not total-order enumeration.
- **`runtime`** (`mod` + `replay`) — process bodies are stackless coroutines registered as
  re-runnable `Fn` factories; `next(traces)` recreates each body and polls it once with a
  no-op waker, replaying committed events and stopping at the first new one. Knows nothing
  about graphs.
- **`program`** — the `Program` trait, the runtime↔explorer boundary. **Read its module
  docs: the `traces` contract is subtle** — `traces[i]` has one `Option<Val>` per
  *event* of thread `i` in po (not per receive), which is what lets the explorer enumerate
  several sends between two receives.
- **`scheduler`** — `next_P` policy: addability (send/error/non-blocking-recv always;
  *blocking* recv only when an unread matching send exists) and Terminal→Full/Blocked
  classification. Rescheduling is automatic — addability is recomputed on the current
  graph every call. Blocking is scheduler state, **not** a `B` event in the graph.
- **`explorer`** (`mod` + `revisit` + `execution` + `parallel`) —
  `explore(make_program, &observer, Config)` runs Algorithm 1, returning nothing (results
  reach you through the observer). `Config::threads > 1` fans the independent subtrees out
  across workers that share the one `&observer` (`parallel`); `make_program` rebuilds the
  `!Send` runtime per worker. `mod` is `Visit` (lines 2–16); `revisit` is the
  backward-revisit half (lines 10–13, 17–22) with `RevisitCondition` and
  `GetConsTiebreaker`. Every recursive branch works on a **clone** of the graph.
- **`observer` / `render`** — `Observer` trait, callbacks `&self` so one observer is shared
  across workers (Null / Counting (per-worker sharded atomics) / Recording / ExecutionCollector
  + tuple composition); text renderer. `Execution::pending_sends()` exposes the unread sends
  (the seam for the time-intervals extension).

## Invariants that are easy to break (all guarded by tests; see §9.4)

These caused real bugs during development and are the first places to look on a regression:

- **Backward revisit** (`revisit.rs`): `Deleted` uses *strict* `<_G`; the revisiting send
  `e` is formally in `Deleted` but **stays in the graph** (keep = `E \ (Deleted \ {e})`);
  `set_rf(r, e)` happens *after* `restrict`. `Previous` uses *non-strict* `≤_G` plus the
  *strict* porf-prefix of `s`. `RevisitCondition` must be checked over `Deleted ∪ {r}`,
  and its blocking-receive case runs the tiebreaker on `G|_Previous`, not full `G`.
- **`GetConsTiebreaker`** must remove `e`'s own rf edge before searching candidates —
  otherwise every revisit dies (e.g. s+s+r drops from 2 to 1). It is a pure function of
  `(E, po, rf\{e}, e)`; no `HashMap`, no dependence on stamps.
- **⊥ semantics** (phase B): ⊥ can be read by *multiple* non-blocking receives at once
  (unlike a send, read ≤1×); a *blocking* receive reading ⊥ is inconsistent; ⊥ is never
  dropped from the line-7 source enumeration and is valid even when matching sends exist.
  `nnr(N)` must be 1, not 2^N.
- **Receives carry no model** in this API (only sends do) — an intentional deviation (O1);
  `consistent_M` runs on the *full* graph (no physical `G|_{E^M}` restriction) because
  porf must traverse foreign-model events.
- **Determinism**: iteration order feeds the tiebreaker and dedup, so use ordered
  containers (`BTree*`/`Vec`) throughout — never `HashMap` where it can affect results.

## Working discipline

- **Never fit a test to a wrong number.** If an oracle count disagrees with the paper,
  that is an explorer bug: stop, document the divergence (program, expected, actual,
  hypothesis), and hand it to the `must-debugger` agent. Do not change the oracle.
- The **fuzz harness** (`tests/fuzz.rs`) is the strongest regression: it diffs the
  explorer's full ∪ blocked terminal set against an independent brute-force enumeration of
  ⟦P⟧ over ~1050 random programs under every priority permutation. Extending the model
  (new receive kinds, time) means extending the brute-force reference too, or it silently
  stops covering the new behavior.
- Development uses the `must-*` subagents (in `../.Codex/agents/`): `must-expert`
  (theory / design / paper cross-checks), `must-implementer` (writes code), `must-impl-reviewer`
  (static review against §9.4), `must-debugger` (execution-count mismatches). The
  established loop is implement → review → fix.

## Planned extension: time intervals

The intended next phase (see `../must_konspekt.md` §11) adds delivery intervals to sends
and deadlines to `recv_timeout`, as a new `consistent_time` predicate. The hard
constraint: any new consistency predicate **must satisfy the §3.2.1 requirements
(No-OOTA, Prefix-closedness, Conditional Extensibility)**, or Theorem 4.1 (soundness /
completeness / optimality) no longer transfers. This phase will modify the core (unlike
phases A/B, which are done) — the "⊥ is always valid" rule in phase B is the first thing
that changes (a timeout becomes inconsistent when a message is guaranteed to arrive
first).
