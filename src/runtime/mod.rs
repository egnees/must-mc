//! Processes as stackless coroutines that implement [`Program`] by replay. A [`System`]
//! registers process bodies as re-runnable factories; computing `next(traces)` re-creates
//! each body and polls it once, letting the trace replay the events already in the graph
//! and stopping at the first new one.
//!
//! This module knows nothing about execution graphs, consistency or the explorer - it
//! depends only on `event` and `program`.
//!
//! ## Contract and honest limitations
//!
//! A process body must be a pure function of the values it receives, and cooperatively
//! bounded:
//! * A pure CPU loop with no API calls (e.g. `loop {}`) cannot be interrupted: the event
//!   budget only bounds bodies that reach `send`/`recv`/`assert_that`. A synchronous loop
//!   that never awaits never yields control, so bounding it is the caller's job (unroll it,
//!   or add a step limit in the body).
//! * Signal assertion failures with [`Ctx::assert_that`] (which emits `Label::Error`),
//!   never `panic!` - a `panic!` inside a body crashes the checker.
//! * A body may only `.await` the futures returned by [`Ctx::recv`], [`Ctx::recv_timeout`]
//!   and [`Ctx::nondet`]. Awaiting any other future is reported as a `Label::Error`.

mod replay;

use std::cell::RefCell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;

use crate::event::{Model, Tid, Val, Window};
use crate::program::{Program, ThreadNext};

use replay::{run_once, ThreadCell};

/// The boxed, pinned future produced by a process body - polled with a no-op waker.
pub type LocalFut = Pin<Box<dyn Future<Output = ()>>>;

/// A receive predicate closure, boxed so it can be stored and later moved into a
/// `Label::Recv`. `Send + Sync` so the resulting `Pred`/`Label`/`ExecutionGraph` can
/// cross threads (see [`crate::event::Pred`]).
pub(crate) type BoxedPred = Box<dyn Fn(&str) -> bool + Send + Sync>;

/// Default per-thread event budget: a body emitting more events than this yields
/// `Label::Error` rather than diverging.
pub const DEFAULT_MAX_EVENTS: usize = 10_000;

/// A system of processes. Each process is stored as a factory `Fn(Ctx) -> LocalFut` so
/// it can be re-executed from scratch on every replay; the checker never keeps a
/// suspended coroutine around.
pub struct System {
    factories: Vec<Box<dyn Fn(Ctx) -> LocalFut>>,
    max_events: usize,
}

impl Default for System {
    fn default() -> Self {
        System::new()
    }
}

impl System {
    pub fn new() -> Self {
        System {
            factories: Vec::new(),
            max_events: DEFAULT_MAX_EVENTS,
        }
    }

    /// Set the per-thread event budget (see [`DEFAULT_MAX_EVENTS`]).
    pub fn with_max_events(mut self, max_events: usize) -> Self {
        self.max_events = max_events;
        self
    }

    /// Register a process body; returns its thread id (`0`-based, in registration
    /// order). `body` is a `Fn` (not `FnOnce`) because it is re-run on every replay.
    pub fn add<F, Fut>(&mut self, body: F) -> Tid
    where
        F: Fn(Ctx) -> Fut + 'static,
        Fut: Future<Output = ()> + 'static,
    {
        let tid = self.factories.len();
        self.factories
            .push(Box::new(move |ctx| Box::pin(body(ctx)) as LocalFut));
        tid
    }

    /// Replay thread `tid` against `trace` and read off its next event.
    fn run_thread(&self, tid: Tid, trace: Vec<Option<Val>>) -> ThreadNext {
        let cell = Rc::new(RefCell::new(ThreadCell::new(trace, self.max_events)));
        let ctx = Ctx {
            tid,
            cell: cell.clone(),
        };
        let fut = (self.factories[tid])(ctx);
        run_once(fut, &cell)
    }
}

impl Program for System {
    fn num_threads(&self) -> usize {
        self.factories.len()
    }

    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        debug_assert_eq!(
            traces.len(),
            self.num_threads(),
            "expected one trace per thread"
        );
        (0..self.factories.len())
            .map(|tid| {
                let trace = traces.get(tid).cloned().unwrap_or_default();
                self.run_thread(tid, trace)
            })
            .collect()
    }

    /// Per-thread replay: re-run only thread `tid`'s body, not all of them.
    fn next_thread(&self, tid: Tid, trace: &[Option<Val>]) -> ThreadNext {
        self.run_thread(tid, trace.to_vec())
    }
}

/// What a process body sees. Its methods drive the per-thread replay of the trace; the
/// body itself must be a pure function of the values it receives.
pub struct Ctx {
    tid: Tid,
    cell: Rc<RefCell<ThreadCell>>,
}

impl Ctx {
    /// This process's thread id.
    pub fn tid(&self) -> Tid {
        self.tid
    }

    /// Send `msg` to thread `to` under communication model `model` (fire-and-forget).
    /// Synchronous: emits a `Label::Send`. Sending to oneself (`to == self.tid()`) is
    /// allowed. Equivalent to `send_within(to, msg, model, Window::ASAP)`.
    pub fn send(&self, to: Tid, msg: impl Into<Val>, model: Model) {
        self.cell
            .borrow_mut()
            .record_send(to, msg.into(), model, Window::ASAP);
    }

    /// Like [`send`](Self::send) but with a delivery [`Window`] on the message: it arrives
    /// at some time in `occ(s) + window` under the time-intervals extension. An ordinary
    /// [`send`](Self::send) is `send_within(.., Window::ASAP)`.
    pub fn send_within(&self, to: Tid, msg: impl Into<Val>, model: Model, window: Window) {
        self.cell
            .borrow_mut()
            .record_send(to, msg.into(), model, window);
    }

    /// Blocking selective receive: awaits a message satisfying `pred` and returns it.
    /// During replay it resolves to the value the graph already gave this receive; if
    /// this is the thread's next event it parks, emitting `Label::Recv`.
    pub fn recv(&self, pred: impl Fn(&str) -> bool + Send + Sync + 'static) -> RecvFuture {
        RecvFuture {
            cell: self.cell.clone(),
            pred_fn: Some(Box::new(pred)),
        }
    }

    /// Non-blocking selective receive: awaits a message satisfying `pred` and returns
    /// `Some(v)`, or `None` when the timeout fires (reading no message). When it parks it
    /// emits `Label::recv_nb`.
    ///
    /// In the DPOR, "no message" is an extra rf source on top of every consistent send,
    /// and - unlike a send - may be read by several non-blocking receives at once. This is
    /// deliberately not a nondet-encoded timeout: N threads each doing one `recv_timeout`
    /// explore exactly one execution, not `2^N`.
    pub fn recv_timeout(
        &self,
        pred: impl Fn(&str) -> bool + Send + Sync + 'static,
    ) -> RecvTimeoutFuture {
        RecvTimeoutFuture {
            cell: self.cell.clone(),
            pred_fn: Some(Box::new(pred)),
        }
    }

    /// Data non-determinism (ND, Algorithm 1 lines 6 and 19): returns some value of the
    /// finite option set `set`. The DPOR enumerates every value of `set`; during replay it
    /// resolves to the value already committed for this choice, or - when this is the
    /// thread's next event - parks and emits `Label::nondet(set)`. `set` must be non-empty.
    pub fn nondet(&self, set: impl IntoIterator<Item = impl Into<Val>>) -> NondetFuture {
        NondetFuture {
            cell: self.cell.clone(),
            set: Some(set.into_iter().map(Into::into).collect()),
        }
    }

    /// Assertion: if `cond` is false, emit `Label::Error` as this thread's next event
    /// (line 5 of Algorithm 1). A holding assertion is pure control flow.
    pub fn assert_that(&self, cond: bool, msg: &str) {
        self.cell.borrow_mut().record_assert(cond, msg);
    }
}

/// Future returned by [`Ctx::recv`]; resolves to the received message.
pub struct RecvFuture {
    cell: Rc<RefCell<ThreadCell>>,
    /// Predicate closure, moved into the emitted `Label::Recv` when the receive parks.
    pred_fn: Option<BoxedPred>,
}

impl Future for RecvFuture {
    type Output = String;

    fn poll(self: Pin<&mut Self>, _cx: &mut std::task::Context<'_>) -> std::task::Poll<String> {
        use std::task::Poll;
        // RecvFuture is Unpin (Rc + Option<Box>), so projecting the fields is safe.
        let this = self.get_mut();
        let mut cell = this.cell.borrow_mut();
        // The graph stores payloads as interned `Sym`s; the process body works in `String`,
        // so resolve at the await boundary.
        match cell.poll_recv(&mut this.pred_fn, true) {
            Poll::Ready(Some(v)) => Poll::Ready(crate::intern::resolve(v).to_owned()),
            // A blocking receive never resolves to `None`: on a committed no-message read
            // `poll_recv` blocks the thread and returns `Pending` instead of `Ready(None)`.
            Poll::Ready(None) => unreachable!("blocking receive resolved to nothing"),
            Poll::Pending => Poll::Pending,
        }
    }
}

/// Future returned by [`Ctx::recv_timeout`]; resolves to `Some(v)` for a received message
/// or `None` when the timeout fires (no message). Unlike [`RecvFuture`], a committed
/// no-message read resolves the future rather than blocking the thread.
pub struct RecvTimeoutFuture {
    cell: Rc<RefCell<ThreadCell>>,
    /// Predicate closure, moved into the emitted `Label::recv_nb` when the receive parks.
    pred_fn: Option<BoxedPred>,
}

impl Future for RecvTimeoutFuture {
    type Output = Option<String>;

    fn poll(
        self: Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<String>> {
        // RecvTimeoutFuture is Unpin (Rc + Option<Box>), so projecting the fields is safe.
        let this = self.get_mut();
        let mut cell = this.cell.borrow_mut();
        // Resolve the interned payload to a `String` for the body (see `RecvFuture::poll`).
        match cell.poll_recv(&mut this.pred_fn, false) {
            std::task::Poll::Ready(opt) => {
                std::task::Poll::Ready(opt.map(|v| crate::intern::resolve(v).to_owned()))
            }
            std::task::Poll::Pending => std::task::Poll::Pending,
        }
    }
}

/// Future returned by [`Ctx::nondet`]; resolves to the chosen nondet value. Like
/// [`RecvFuture`] it is a real `Future` so replay can park at the choice point: a nondet
/// value already committed in the trace resolves immediately, otherwise the choice parks
/// and emits `Label::nondet(set)`. A nondet event never resolves to nothing.
pub struct NondetFuture {
    cell: Rc<RefCell<ThreadCell>>,
    /// Option set, moved into the emitted `Label::nondet` when the choice parks.
    set: Option<Vec<Val>>,
}

impl Future for NondetFuture {
    type Output = String;

    fn poll(self: Pin<&mut Self>, _cx: &mut std::task::Context<'_>) -> std::task::Poll<String> {
        // NondetFuture is Unpin (Rc + Option<Vec>), so projecting the fields is safe.
        let this = self.get_mut();
        let mut cell = this.cell.borrow_mut();
        // Resolve the interned choice to a `String` for the body (see `RecvFuture::poll`).
        match cell.poll_nondet(&mut this.set) {
            std::task::Poll::Ready(v) => {
                std::task::Poll::Ready(crate::intern::resolve(v).to_owned())
            }
            std::task::Poll::Pending => std::task::Poll::Pending,
        }
    }
}
