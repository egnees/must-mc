//! Replay mechanics: the per-thread coroutine cell and the driver that polls a process
//! body once to compute its next event.
//!
//! For each `next(traces)` query and each thread, the runtime re-creates the process
//! future from its factory and polls it once with a no-op waker. During that poll,
//! `Ctx::send` / `RecvFuture` / `Ctx::assert_that` drive a shared [`ThreadCell`] that
//! replays the events already fixed by the trace and stops at the first event not yet in
//! the graph.

use std::cell::RefCell;
use std::task::{Context, Poll, Waker};

use crate::event::{Label, Model, ReceiveTiming, Tid, Val, Window};
use crate::program::{ThreadNext, TraceLabel};

use super::{LocalFut, RecvPredicate};

thread_local! {
    /// `"recv#k"` tags, built once per `k` and shared by every `Pred` for that position.
    /// A receive label is emitted on essentially every replay, and the `format!` behind that
    /// tag was one of the largest single costs in the untimed profile; the tag is a pure
    /// function of `k`, so caching it is byte-identical.
    static RECV_TAGS: RefCell<Vec<std::sync::Arc<str>>> = const { RefCell::new(Vec::new()) };
}

/// The cached `"recv#k"` tag.
fn recv_tag(k: usize) -> std::sync::Arc<str> {
    RECV_TAGS.with(|tags| {
        let mut tags = tags.borrow_mut();
        while tags.len() <= k {
            let next = tags.len();
            tags.push(std::sync::Arc::from(format!("recv#{next}").as_str()));
        }
        tags[k].clone()
    })
}

/// Outcome recorded while replaying a single poll of a process body.
enum Halt {
    /// Still replaying events already fixed by the trace.
    Running,
    /// The first event not yet in the graph (this thread's next event).
    Emit(Label),
    /// The thread has no next event under this trace (`P_i(trace)` is nothing): either the
    /// body ran to completion, or a blocking receive read no message, or an
    /// already-committed error terminated it.
    Finished,
}

enum Resume {
    Receive {
        value: Option<Val>,
        blocking: bool,
        timing: ReceiveTiming,
    },
    Nondet(Val),
}

/// Shared state a process body reads and writes through its [`Ctx`](super::Ctx) during
/// one replay poll. Single-threaded (`Rc`/`RefCell`).
pub(crate) struct ThreadCell {
    /// The per-event trace of this thread (see `program.rs`): one entry per event already
    /// in the graph, in po. Sends and errors are `None`; a receive is its read value
    /// (`Some(v)`, or `None` for no message).
    trace: Vec<Option<Val>>,
    /// Position among all events (index into `trace`); advanced by every committed
    /// send/receive so the cursor tracks po position.
    cursor: usize,
    /// Count of receives reached so far this poll; gives each receive a stable `recv#k`
    /// predicate tag (deterministic per po position).
    recv_index: usize,
    /// Number of events emitted/replayed this poll; bounds divergent bodies.
    op_count: usize,
    /// Per-thread event budget: exceeding it yields `Label::Error` instead of looping
    /// forever.
    max_events: usize,
    /// Per-thread receive budget (`System::set_max_recvs`): the body's `(max_recvs + 1)`-th
    /// receive halts the thread as `Finished` instead of becoming an event. `usize::MAX`
    /// (the default) means unbounded.
    max_recvs: usize,
    /// Collected only when reconstructing execution annotations, not on ordinary next().
    labels: Option<Vec<TraceLabel>>,
    halt: Halt,
    /// A parked await was already charged and emitted its predicate/option set.
    /// Its next poll consumes this committed reply instead of emitting it again.
    resume: Option<Resume>,
    /// Opt-in run-ahead: freshly computed synchronous sends advance a virtual
    /// trace and are returned as separate next-event answers for its prefixes.
    batch: Option<Vec<Label>>,
}

impl ThreadCell {
    pub(crate) fn new(
        trace: Vec<Option<Val>>,
        max_events: usize,
        max_recvs: usize,
        collect_labels: bool,
    ) -> Self {
        ThreadCell {
            trace,
            cursor: 0,
            recv_index: 0,
            op_count: 0,
            max_events,
            max_recvs,
            labels: collect_labels.then(Vec::new),
            halt: Halt::Running,
            resume: None,
            batch: None,
        }
    }

    pub(crate) fn matches_trace(&self, trace: &[Option<Val>]) -> bool {
        self.trace == trace
    }

    pub(crate) fn extends_trace_once(&self, trace: &[Option<Val>]) -> bool {
        trace.len() == self.trace.len() + 1 && trace[..self.trace.len()] == self.trace
    }

    pub(crate) fn has_labels(&self) -> bool {
        self.labels.is_some()
    }

    pub(crate) fn labels_snapshot(&self) -> Vec<TraceLabel> {
        self.labels
            .as_ref()
            .expect("checkpoint collects annotations")
            .clone()
    }

    pub(crate) fn begin_batch(&mut self) {
        self.batch = Some(Vec::new());
    }

    pub(crate) fn begin_plain(&mut self) {
        self.batch = None;
    }

    pub(crate) fn finish_batch(&mut self, next: ThreadNext) -> (Vec<ThreadNext>, Vec<TraceLabel>) {
        let mut steps: Vec<_> = self
            .batch
            .take()
            .expect("batch mode was started")
            .into_iter()
            .map(ThreadNext::Next)
            .collect();
        steps.push(next);
        (
            steps,
            self.labels
                .as_ref()
                .expect("batch collects annotations")
                .clone(),
        )
    }

    pub(crate) fn resume_with(&mut self, value: Option<Val>) {
        debug_assert_eq!(self.cursor, self.trace.len());
        self.resume = Some(match &self.halt {
            Halt::Emit(Label::Recv {
                blocking, timing, ..
            }) => Resume::Receive {
                value,
                blocking: *blocking,
                timing: *timing,
            },
            Halt::Emit(Label::Nondet { .. }) => {
                Resume::Nondet(value.expect("a nondet event never reads nothing"))
            }
            _ => unreachable!("only a parked receive or nondet future can resume"),
        });
        self.trace.push(value);
        self.halt = Halt::Running;
    }

    fn halted(&self) -> bool {
        !matches!(self.halt, Halt::Running)
    }

    pub(crate) fn insert_label(&mut self, tid: Tid, value: Val) {
        // Synchronous sends/assertions can leave the Rust body running after the
        // first new event. Such a tail is outside the committed trace.
        if self.halted() {
            return;
        }
        if let Some(labels) = &mut self.labels {
            labels.push(TraceLabel {
                tid,
                position: self.cursor,
                value,
            });
        }
    }

    pub(crate) fn take_labels(&mut self) -> Vec<TraceLabel> {
        self.labels.take().unwrap_or_default()
    }

    /// Charge one operation against the event budget; returns `true` (and halts) once the
    /// budget is exhausted. The budget-error halt uses the same terminal dispatch as any
    /// other error: if the offending position is still inside the trace the error is
    /// already committed, so the thread is `Finished`; only a fresh position emits a new
    /// `Error` event. (Otherwise a long trace over a divergent body would re-emit `Error`
    /// forever, which is exactly the divergence the budget must stop.)
    fn over_budget(&mut self) -> bool {
        self.op_count += 1;
        if self.op_count > self.max_events {
            if self.cursor < self.trace.len() {
                self.cursor += 1;
                self.halt = Halt::Finished;
            } else {
                self.halt = Halt::Emit(Label::error("event limit exceeded"));
            }
            true
        } else {
            false
        }
    }

    /// `Ctx::send`. If this send is still within the trace it is already in the graph
    /// (advance past it); otherwise it is this thread's next event.
    pub(crate) fn record_send(&mut self, to: Tid, msg: Val, model: Model, window: Window) {
        if self.halted() || self.over_budget() {
            return;
        }
        if self.cursor < self.trace.len() {
            // An already-committed send carries no value in its trace slot (None); a
            // Some(v) here would mean trace extraction is out of sync with the events.
            debug_assert!(
                self.trace[self.cursor].is_none(),
                "send position must carry a None (nothing) trace entry, got a value"
            );
            self.cursor += 1;
        } else {
            let label = Label::send_within(model, to, msg, window);
            if let Some(batch) = &mut self.batch {
                batch.push(label);
                self.trace.push(None);
                self.cursor += 1;
            } else {
                self.halt = Halt::Emit(label);
            }
        }
    }

    /// `RecvFuture::poll` (blocking) / `RecvTimeoutFuture::poll` (non-blocking). Takes
    /// ownership of the predicate closure so it can be moved into the emitted `Label::Recv`
    /// when this receive is the next event.
    ///
    /// The `blocking` flag selects the receive flavour and what a committed no-message read
    /// means:
    ///   * a blocking receive that read no message blocks the thread (`Finished`);
    ///   * a non-blocking receive (`recv_timeout`) that read no message resolves to `None`
    ///     and the thread continues - the timeout fired.
    ///
    /// Returns `Poll::Ready(Some(v))` for a value, `Poll::Ready(None)` for a no-message
    /// read that resolves the future (non-blocking only), and `Poll::Pending` when the
    /// thread parks (recording the receive) or blocks.
    ///
    /// A committed receive position may legally carry either `Some(v)` or `None` (a
    /// non-blocking receive may have read no message), so - unlike send/error positions -
    /// there is intentionally no trace-shape assertion here. The blocking-vs-non-blocking
    /// distinction is structural: it comes from which API the replayed body called at this
    /// cursor position, never from the shape of the trace entry.
    pub(crate) fn poll_recv(
        &mut self,
        pred_fn: &mut Option<RecvPredicate>,
        blocking: bool,
        timing: ReceiveTiming,
    ) -> Poll<Option<Val>> {
        // Once we have recorded the next event (or finished), further awaits just park
        // so the top-level poll unwinds; the recorded outcome takes priority.
        if self.halted() {
            return Poll::Pending;
        }
        if pred_fn.is_none() {
            match self.resume.take() {
                Some(Resume::Receive {
                    value,
                    blocking: parked_blocking,
                    timing: parked_timing,
                }) => {
                    assert_eq!(blocking, parked_blocking);
                    assert_eq!(timing, parked_timing);
                    self.cursor += 1;
                    return match value {
                        None if blocking => {
                            self.halt = Halt::Finished;
                            Poll::Pending
                        }
                        value => Poll::Ready(value),
                    };
                }
                _ => panic!("recv future polled twice after parking"),
            }
        }
        // A different future cannot consume the saved reply of the parked await.
        if self.resume.is_some() || self.over_budget() {
            return Poll::Pending;
        }
        // Receive budget: the thread's `max_recvs` receives are its last events, so the
        // next one is not an event at all - the thread has no next event and is
        // `Finished`. `recv_index` counts the receives *reached in this poll*, replayed
        // ones included, so the cut is a pure function of the trace (the same bound the
        // body would impose with its own `for _ in 0..max_recvs` loop). A body past the
        // budget has replayed its whole trace, so `cursor == trace.len()` still holds for
        // `run_once`'s finished-thread check.
        if self.recv_index >= self.max_recvs {
            self.halt = Halt::Finished;
            return Poll::Pending;
        }
        let k = self.recv_index;
        self.recv_index += 1;
        if self.cursor < self.trace.len() {
            let value = self.trace[self.cursor];
            self.cursor += 1;
            match value {
                Some(v) => Poll::Ready(Some(v)),
                // No-message read: a blocking receive blocks the thread, a non-blocking
                // one resolves to `None` and continues (timeout).
                None if blocking => {
                    self.halt = Halt::Finished;
                    Poll::Pending
                }
                None => Poll::Ready(None),
            }
        } else {
            // This receive is the next event: park and record it (blocking or not).
            let f = pred_fn
                .take()
                .expect("recv future polled twice after parking");
            let pred = match f {
                RecvPredicate::Any => crate::event::Pred::any_with_repr(recv_tag(k)),
                RecvPredicate::Custom(f) => crate::event::Pred::from_boxed(recv_tag(k), f),
            };
            let label = match timing {
                ReceiveTiming::Abstract if blocking => Label::recv(pred),
                ReceiveTiming::Abstract => Label::recv_nb(pred),
                ReceiveTiming::Timeout(window) => Label::recv_timeout_timed(pred, window),
                ReceiveTiming::Poll(window) => Label::recv_poll_timed(pred, window),
            };
            self.halt = Halt::Emit(label);
            Poll::Pending
        }
    }

    /// `NondetFuture::poll`. Mirrors `poll_recv` but for a data non-determinism choice
    /// (ND, Algorithm 1 line 6): it never touches `recv_index`, a committed slot is always
    /// a value (a nondet event never reads nothing), and parking emits `Label::nondet(set)`.
    /// Advances `cursor` on a committed replay so po position stays in step.
    pub(crate) fn poll_nondet(&mut self, set: &mut Option<Vec<Val>>) -> Poll<Val> {
        // Once the next event is recorded (or the thread finished) further awaits park.
        if self.halted() {
            return Poll::Pending;
        }
        if set.is_none() {
            match self.resume.take() {
                Some(Resume::Nondet(value)) => {
                    self.cursor += 1;
                    return Poll::Ready(value);
                }
                _ => panic!("nondet future polled twice after parking"),
            }
        }
        if self.resume.is_some() || self.over_budget() {
            return Poll::Pending;
        }
        if self.cursor < self.trace.len() {
            let value = self.trace[self.cursor];
            self.cursor += 1;
            match value {
                Some(v) => Poll::Ready(v),
                None => unreachable!("a nondet event never reads nothing"),
            }
        } else {
            // This nondet choice is the next event: park and record it.
            let s = set
                .take()
                .expect("nondet future polled twice after parking");
            self.halt = Halt::Emit(Label::nondet(s));
            Poll::Pending
        }
    }

    /// `Ctx::assert_that`. A holding assertion is pure control flow (no event); a
    /// violated assertion is an `Error` event.
    pub(crate) fn record_assert(&mut self, cond: bool, msg: &str) {
        if cond || self.halted() || self.over_budget() {
            return;
        }
        if self.cursor < self.trace.len() {
            // Error already committed; the thread terminates afterwards. Its trace slot
            // carries no value (None); a value would signal a trace mismatch.
            debug_assert!(
                self.trace[self.cursor].is_none(),
                "error position must carry a None (nothing) trace entry, got a value"
            );
            self.cursor += 1;
            self.halt = Halt::Finished;
        } else {
            self.halt = Halt::Emit(Label::error(msg));
        }
    }
}

/// Drive `fut` (a freshly created process body) through one poll and read off the
/// thread's next event. The `std::task::Waker::noop()` waker is enough because our
/// futures never register a waker: they drive synchronously, returning `Ready` to
/// finish and `Pending` to park (with the outcome already stored in the cell).
pub(crate) fn run_once(mut fut: LocalFut, cell: &RefCell<ThreadCell>) -> ThreadNext {
    poll_once(&mut fut, cell).0
}

/// Return whether this poll stopped exactly at a resumable provided await.
/// Synchronous sends may execute their Rust tail before parking elsewhere, so
/// their futures must never be retained as checkpoints of the emitted send.
pub(crate) fn poll_once(fut: &mut LocalFut, cell: &RefCell<ThreadCell>) -> (ThreadNext, bool) {
    let mut cx = Context::from_waker(Waker::noop());
    let future_done = fut.as_mut().poll(&mut cx).is_ready();
    let cell = cell.borrow();
    let outcome = match &cell.halt {
        Halt::Emit(label) => ThreadNext::Next(label.clone()),
        Halt::Finished => ThreadNext::Finished,
        Halt::Running => {
            if future_done {
                // The body returned `()`: all its events were replayed, none new.
                ThreadNext::Finished
            } else {
                // The body parked without recording an event: it awaited a future that is
                // not one of ours and did not resolve synchronously. This is outside the
                // contract (bodies may only await the provided futures); report it as an
                // error rather than a silent - and unsound - `Finished`.
                ThreadNext::Next(Label::error("body awaited a foreign future"))
            }
        }
    };
    // A non-budget `Finished` must have consumed the whole trace; a leftover entry means
    // the trace was longer than this body's event sequence (an extraction bug). The
    // budget-truncation path legitimately finishes early, so it is exempt.
    debug_assert!(
        !outcome.is_finished()
            || cell.op_count > cell.max_events
            || cell.cursor == cell.trace.len(),
        "body finished with {} of {} trace entries consumed",
        cell.cursor,
        cell.trace.len(),
    );
    // A custom predicate can capture body-local shared mutable state. Keeping
    // its future alive would let continuation code mutate a predicate already
    // stored in an older execution graph. Only constructor-proven Any receives
    // and immutable nondet option sets have no such mutable capture.
    let resumable = !future_done
        && match &cell.halt {
            Halt::Emit(Label::Recv { pred, .. }) => pred.is_any(),
            Halt::Emit(Label::Nondet { .. }) => true,
            _ => false,
        };
    (outcome, resumable)
}
