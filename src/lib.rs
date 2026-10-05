//! A model checker for message-passing concurrency.
//!
//! `must` explores every distinct way the messages of a distributed protocol can be
//! delivered and checks your assertions against all of them. It implements the Must
//! optimal dynamic partial-order reduction (Enea et al., "Model Checking Distributed
//! Protocols in Must", OOPSLA 2024): each meaningfully different execution is visited
//! exactly once, with no duplicate interleavings.
//!
//! # Example
//!
//! Two peers race to send one message; a third thread receives one of them. The checker
//! finds both outcomes and nothing else. `explore` builds the system afresh (once here,
//! once per worker in a parallel run) and reports every outcome to the observer.
//!
//! ```
//! use must::event::Model;
//! use must::{explore, Config, CountingObserver, Ctx, System};
//!
//! let counter = CountingObserver::new();
//! explore(
//!     || {
//!         let mut sys = System::new();
//!         sys.add(|c: Ctx| async move { c.send(2, "ping", Model::P2p); });
//!         sys.add(|c: Ctx| async move { c.send(2, "pong", Model::P2p); });
//!         sys.add(|c: Ctx| async move {
//!             let _msg = c.recv(|_| true).await;
//!         });
//!         sys
//!     },
//!     &counter,
//!     Config::default(),
//! );
//! assert_eq!(counter.full(), 2); // reads "ping", or reads "pong"
//! ```
//!
//! # Writing a process
//!
//! A process is an `async` block driven by a [`Ctx`]. It reads like ordinary code; the
//! checker replays it under every consistent message ordering.
//!
//! - [`Ctx::send`] delivers a message under a chosen communication [`Model`].
//! - [`Ctx::recv`] blocks for a matching message; [`Ctx::recv_timeout`] may instead
//!   return `None`, modelling a timeout.
//! - [`Ctx::nondet`] explores every value of a finite set (data non-determinism).
//! - [`Ctx::assert_that`] reports a safety violation.
//!
//! Assertion failures, deadlocks, and non-terminating processes each surface as a
//! distinct terminal outcome, reported to the observer.
//!
//! # How it works
//!
//! Every execution is an *execution graph*: events ordered per thread by program order
//! (`po`), plus a reads-from relation (`rf`) linking each receive to the send it read
//! (or to nothing, for a timeout). A communication model decides which graphs are
//! *consistent*, i.e. which delivery orders are allowed. [`explore`] enumerates each
//! consistent graph once, notifying an observer at every outcome.
//!
//! # Modules
//!
//! - [`event`]: events, labels, and the communication [`Model`].
//! - [`graph`]: the execution graph and its queries.
//! - [`consistency`]: well-formedness and the per-model consistency predicates.
//! - [`runtime`]: the [`System`]/[`Ctx`] API that turns `async` processes into a
//!   [`Program`].
//! - [`scheduler`]: the scheduling policy the explorer follows.
//! - [`explorer`]: the exploration itself, [`explore`].
//! - [`observer`] / [`render`]: inspecting and displaying a run.
//! - [`viz`]: dumping a run as a `must-viz` JSON trace for the visualizer.

pub mod consistency;
pub mod event;
pub mod explorer;
pub mod graph;
pub mod intern;
pub mod observer;
pub mod program;
pub mod render;
pub mod runtime;
pub mod scheduler;
pub mod time;
pub mod viz;

pub use consistency::{
    consistent, consistent_asyn, consistent_cd, consistent_mbox, consistent_p2p, well_formed,
};
pub use event::{Event, EventId, Label, Model, Pred, Tid, Val, Window};
pub use explorer::{explore, Config, Execution, ExecutionKind};
pub use graph::ExecutionGraph;
pub use observer::{
    CountingObserver, DeadBranchDetector, ExecutionCollector, NullObserver, Observer,
    RecordingObserver, Step, StepKind,
};
pub use program::{Program, ThreadNext};
pub use runtime::{Ctx, NondetFuture, RecvFuture, RecvTimeoutFuture, System, DEFAULT_MAX_EVENTS};
pub use scheduler::{next_step, traces_of, NextStep};
pub use time::{check, eager_feasible, TimedVerdict};
pub use viz::{Summary as TraceSummary, TraceObserver};
