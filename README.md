# must-mc

[![crates.io](https://img.shields.io/crates/v/must-mc.svg)](https://crates.io/crates/must-mc)
[![docs.rs](https://img.shields.io/docsrs/must-mc)](https://docs.rs/must-mc)
[![license](https://img.shields.io/crates/l/must-mc.svg)](#license)

A model checker for message-passing concurrency. `must` explores **every**
distinct way the messages of a distributed protocol can be delivered, and checks
your assertions against all of them. It is a from-scratch Rust implementation of
the **Must** optimal dynamic partial-order reduction (Enea et al., *Model Checking
Distributed Protocols in Must*, OOPSLA 2024).

"Optimal" means each meaningfully different execution is visited exactly once — no
redundant interleavings, no duplicates. That is what makes exhaustive checking of
non-trivial protocols (leader election, replicated logs, commit protocols) feasible.

The published crate is `must-mc`; it is imported as `must`.

```toml
[dependencies]
must-mc = "0.1"
```

## Example

A receiver waits for one message; two peers race to send it. `must` reports both
outcomes — the receiver reading either message — and nothing else.

`explore` builds the system (once here, once per worker in a parallel run) and reports
every outcome to an observer; nothing is returned.

```rust
use must::event::Model;
use must::{explore, Config, CountingObserver, Ctx, System};

let counter = CountingObserver::new();
explore(
    || {
        let mut sys = System::new();
        sys.add(|c: Ctx| async move { c.send(2, "ping", Model::P2p); });
        sys.add(|c: Ctx| async move { c.send(2, "pong", Model::P2p); });
        sys.add(|c: Ctx| async move {
            let _msg = c.recv(|_| true).await;
        });
        sys
    },
    &counter,
    Config::default(),
);

assert_eq!(counter.full(), 2); // reads "ping", or reads "pong"
```

## Writing a process

A process is an `async` block driven by a `Ctx`. It looks like ordinary code; the
checker replays it under every consistent message ordering.

| Method | Meaning |
| --- | --- |
| `c.send(to, msg, model)` | Send `msg` to thread `to` (fire-and-forget). |
| `c.recv(pred).await` | Block until a message matching `pred` arrives; return it. |
| `c.recv_timeout(pred).await` | Like `recv`, but may return `None` — the timeout firing. |
| `c.nondet(set).await` | Explore every value in `set` (data non-determinism). |
| `c.assert_that(cond, msg)` | Report a safety violation when `cond` is false. |

Assertion failures, deadlocks (a blocking `recv` that can never be satisfied), and
non-terminating processes are all surfaced as distinct outcomes, reported to the observer.

## Communication models

Every `send` carries a delivery model, so one program can mix guarantees:

| Model | Delivery guarantee |
| --- | --- |
| `Asyn` | Fully asynchronous — any order. |
| `P2p` | FIFO between each ordered sender/receiver pair. |
| `Cd` | Causal delivery — causally ordered messages arrive in order. |
| `Mbox` | Mailbox — a single arrival order per receiver. |

## Features

- Exhaustive, duplicate-free exploration of all consistent executions.
- Selective receives, timeouts, and data non-determinism.
- Four communication models, mixable per message.
- A parallel explorer (set `Config::threads`) that scales the search across cores.
- Pluggable `Observer`s — count, record, collect, or render runs, or hook every
  step of the search to follow the algorithm's progress in detail.
- Export any run as a JSON trace for external tooling.
- Zero runtime dependencies — pure `std`.

## Running the example

A bounded, Raft-style leader election with crash/recovery and an election-safety
monitor:

```sh
cargo run --release --example raft_election -- --bug   # inject a bug; the monitor catches it
cargo run --release --example raft_election             # correct protocol
```

## References

- Enea, Farzan, Koskinen, et al. *Model Checking Distributed Protocols in Must.*
  OOPSLA 2024.
- Kokologiannakis, Marmanis, Vafeiadis. *Truly Stateless, Optimal Dynamic Partial
  Order Reduction (TruSt).* POPL 2022.

## License

Licensed under either of [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE) at your
option.
