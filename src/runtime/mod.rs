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
//! * An event loop that *does* await may stay `loop { ... }` in the body and be bounded
//!   from outside with [`System::set_max_recvs`]: past its receive budget the thread simply
//!   has no next event. Since bodies are re-created and replayed on every `next` query, a
//!   bound imposed by the body's *driver* (a wrapper future counting polls) counts replays
//!   rather than progress and bounds nothing - it must be a function of the trace.
//! * Signal assertion failures with [`Ctx::assert_that`] (which emits `Label::Error`),
//!   never `panic!` - a `panic!` inside a body crashes the checker.
//! * A body may only `.await` the futures returned by [`Ctx::recv`], [`Ctx::recv_timeout`]
//!   and [`Ctx::nondet`]. Awaiting any other future is reported as a `Label::Error`.

mod replay;

use std::cell::RefCell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;

use crate::event::{Label, Model, Tid, Val, Window};
use crate::program::{Program, ThreadNext};

use replay::{run_once, ThreadCell};

/// The boxed, pinned future produced by a process body - polled with a no-op waker.
pub type LocalFut = Pin<Box<dyn Future<Output = ()>>>;

/// A receive predicate closure, boxed so it can be stored and later moved into a
/// `Label::Recv`. `Send + Sync` so the resulting `Pred`/`Label`/`ExecutionGraph` can
/// cross threads (see [`crate::event::Pred`]).
pub(crate) type BoxedPred = Box<dyn Fn(&str) -> bool + Send + Sync>;

/// A process's declared **future-label** over-approximation: given the thread's trace, the
/// labels its events *strictly after* its next one may carry. See
/// [`System::declare_future`]; `None` (no declaration) means "unknown".
type FutureDecl = Box<dyn Fn(&[Option<Val>]) -> Vec<Label>>;

/// Default per-thread event budget: a body emitting more events than this yields
/// `Label::Error` rather than diverging.
pub const DEFAULT_MAX_EVENTS: usize = 10_000;

/// A system of processes. Each process is stored as a factory `Fn(Ctx) -> LocalFut` so
/// it can be re-executed from scratch on every replay; the checker never keeps a
/// suspended coroutine around.
pub struct System {
    factories: Vec<Box<dyn Fn(Ctx) -> LocalFut>>,
    /// Per-thread future-label declaration ([`System::declare_future`]), parallel to
    /// `factories`. `None` = undeclared = the safe "unknown" answer from
    /// [`Program::possible_future`].
    futures: Vec<Option<FutureDecl>>,
    /// Per-thread receive budget ([`System::set_max_recvs`]), parallel to `factories`.
    /// `usize::MAX` = unbounded.
    recv_budgets: Vec<usize>,
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
            futures: Vec::new(),
            recv_budgets: Vec::new(),
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
        self.futures.push(None); // undeclared future = the safe `None` (see `possible_future`)
        self.recv_budgets.push(usize::MAX); // unbounded until `set_max_recvs` says otherwise
        tid
    }

    /// Bound thread `tid` to at most `max_recvs` receives: its `max_recvs` [`Ctx::recv`] /
    /// [`Ctx::recv_timeout`] calls become events as usual, and the next one instead ends
    /// the thread (no event, no error). Unbounded by default.
    ///
    /// This is how an event loop written as `loop { ... }` — infinite by design, the way a
    /// real protocol is written — is made finite for the checker *from the outside*, so the
    /// process body stays honest. It has to live here rather than in a wrapper future
    /// because a bound is only meaningful if it is a function of the thread's trace: bodies
    /// are re-created and replayed on every [`Program::next`] query (see the module docs),
    /// so a counter kept in the body's driver counts replays, not progress. `recv_index`
    /// counts the receives *reached during the replay*, which is exactly such a function.
    ///
    /// The cut is a bounded-model-checking truncation, identical in effect to writing
    /// `for _ in 0..max_recvs` around the loop inside the body: the thread's terminal is a
    /// normal full/blocked one, not a `Label::Error` (unlike the divergence backstop
    /// [`System::with_max_events`], which reports an error because it fires where no bound
    /// was intended). Sends are not counted, so bound a body whose loop can send without
    /// receiving with [`with_max_events`](Self::with_max_events) too.
    pub fn set_max_recvs(&mut self, tid: Tid, max_recvs: usize) {
        let n = self.factories.len();
        assert!(
            tid < n,
            "set_max_recvs: no such thread {tid} (the system has {n}; `add` returns the tid)"
        );
        self.recv_budgets[tid] = max_recvs;
    }

    /// Declare a **sound over-approximation** of the labels thread `tid`'s events may carry
    /// *strictly after* its next one, as a function of the thread's trace (see
    /// [`crate::program`] for the trace contract). This is the opt-in half of
    /// [`Program::possible_future`]: an undeclared process keeps answering `None`
    /// ("unknown"), which is always safe, so declaring changes nothing for anyone else.
    ///
    /// # The obligation you take on
    ///
    /// For **every** continuation of `trace`, every event of thread `tid` at po-position
    /// `len(trace) + 2` or later must carry a label present in `tail(trace)`. The thread's
    /// *next* label (position `len(trace) + 1`) is supplied by the runtime itself — it
    /// replays the body and knows it exactly — so `tail` must not try to predict it, and
    /// including it anyway is harmless (it only makes the answer coarser).
    ///
    /// A declaration that is too narrow is a **soundness bug**: [`crate::time::force_source`]
    /// uses it to prove a blocking receive's source unavoidable, and an unavoidable-looking
    /// but avoidable read over-prunes, losing realizable terminals. When in doubt, declare
    /// more (a superset is always sound) or do not declare at all.
    ///
    /// Only `dst`/payload of sends and `is_recv`/predicate of receives are ever inspected, so
    /// windows and models in the declared labels are free to be approximate — but the
    /// *payload set* of future sends and the *acceptance set* of future receives must both be
    /// covered.
    pub fn declare_future<F>(&mut self, tid: Tid, tail: F)
    where
        F: Fn(&[Option<Val>]) -> Vec<Label> + 'static,
    {
        let n = self.factories.len();
        assert!(
            tid < n,
            "declare_future: no such thread {tid} (the system has {n}; `add` returns the tid)"
        );
        self.futures[tid] = Some(Box::new(tail));
    }

    /// [`declare_future`](Self::declare_future) with a trace-independent alphabet: the labels
    /// thread `tid` may emit *anywhere* in its remaining run. The coarsest useful declaration
    /// and the easiest to get right — a superset of the process's whole label alphabet is
    /// always sound.
    pub fn declare_alphabet(&mut self, tid: Tid, labels: impl IntoIterator<Item = Label>) {
        let labels: Vec<Label> = labels.into_iter().collect();
        self.declare_future(tid, move |_| labels.clone());
    }

    /// Replay thread `tid` against `trace` and read off its next event.
    fn run_thread(&self, tid: Tid, trace: Vec<Option<Val>>) -> ThreadNext {
        let cell = Rc::new(RefCell::new(ThreadCell::new(
            trace,
            self.max_events,
            self.recv_budgets[tid],
        )));
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

    /// A coroutine body's future is value-dependent (it branches on received messages and
    /// nondet), so its remaining events cannot be enumerated by replay alone. The answer is
    /// therefore **declaration-driven** ([`System::declare_future`]):
    ///
    /// * undeclared (the default) → `None`, "unknown". [`crate::time::force_source`] then
    ///   never forces a blocking receive for this `System` — C1-safe by construction, at the
    ///   cost of a shorter forced closure. Any resulting dead branches are a performance
    ///   matter, never a soundness one.
    /// * declared → the thread's **exact** next label followed by the declared
    ///   over-approximation of everything after it. The head is exact because the runtime can
    ///   simply replay the body for it; that also honours the positional half of the
    ///   [`Program::possible_future`] contract (`labels[0]` is the next event's label), which
    ///   is what lets `force_source` tell the receive it is forcing from the receives that
    ///   might steal its message.
    /// * declared but already `Finished` → `Some(vec![])`, the *exact* answer (a finished
    ///   thread has no future events at all), regardless of what was declared.
    ///
    /// # Cost
    ///
    /// Every `Some` answer re-runs the whole body once ([`System::run_thread`]) to obtain the
    /// exact head. [`crate::time::force_source`] can ask up to once per unfinished thread per
    /// force attempt, and a force attempt happens per blocking receive per closure round, so a
    /// declared system pays roughly one extra body replay per thread per round on top of the
    /// `next` it already does. That is the same order as the closure itself, but it is not free:
    /// declare only where the extra forcing precision is worth it.
    fn possible_future(&self, tid: Tid, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        let tail = self.futures.get(tid)?.as_ref()?;
        let mut out = match self.run_thread(tid, trace.to_vec()) {
            ThreadNext::Next(label) => vec![label],
            ThreadNext::Finished => return Some(Vec::new()),
        };
        out.extend(tail(trace));
        Some(out)
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
