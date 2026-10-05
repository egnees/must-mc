//! Events and labels of the execution graph (Definition 3.1, Enea et al., OOPSLA 2024).

use std::fmt;
use std::sync::Arc;

/// Thread identifier. Threads are numbered `0..N`.
pub type Tid = usize;

/// Message payload: an interned [`Sym`](crate::intern::Sym), a 4-byte `Copy` handle for a
/// string. Build one from a `&str`/`String` via `.into()`; recover the bytes with
/// [`intern::resolve`](crate::intern::resolve). See [`crate::intern`] for the determinism
/// contract.
pub type Val = crate::intern::Sym;

/// Communication model attached to every `send` (Definition 3.1). Receives carry no
/// model; only sends do.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Model {
    Asyn,
    P2p,
    Cd,
    Mbox,
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Model::Asyn => "asyn",
            Model::P2p => "p2p",
            Model::Cd => "cd",
            Model::Mbox => "mbox",
        };
        f.write_str(s)
    }
}

/// Delivery window `[lo, hi]` (closed) of a send: its message arrives at some time in
/// `occ(s) + [lo, hi]` (see the time-intervals extension). `hi = None` is ∞ (no upper
/// bound). Fields are private, so every `Window` is well-formed by construction
/// (`lo <= hi`, bounds `<= MAX_BOUND`) — the only ways to build one validate.
///
/// The default [`ASAP`](Self::ASAP) `= [0, ∞)` is the window of every ordinary
/// [`Label::send`]; a graph whose sends all carry `ASAP` is *untimed* and stays
/// byte-identical to the pre-window key/label format everywhere.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Window {
    lo: u64,
    hi: Option<u64>,
}

impl Window {
    /// `[0, ∞)` — the default window of every untimed send. [`is_untimed`](Self::is_untimed)
    /// is true for exactly this value.
    pub const ASAP: Window = Window { lo: 0, hi: None };

    /// Upper bound on any finite window bound. The time solver sums up to `|E|` edge weights
    /// of magnitude `MAX_BOUND` into an `i64`, so bounds are capped well below `i64::MAX` to
    /// rule out overflow.
    pub const MAX_BOUND: u64 = 1 << 40;

    /// Closed window `[lo, hi]`. Panics on `lo > hi` or `hi > MAX_BOUND`.
    pub fn new(lo: u64, hi: u64) -> Self {
        assert!(lo <= hi, "window lo ({lo}) must not exceed hi ({hi})");
        assert!(
            hi <= Self::MAX_BOUND,
            "window hi ({hi}) must not exceed MAX_BOUND ({})",
            Self::MAX_BOUND
        );
        Window { lo, hi: Some(hi) }
    }

    /// Half-open window `[lo, ∞)`. Panics on `lo > MAX_BOUND`.
    pub fn at_least(lo: u64) -> Self {
        assert!(
            lo <= Self::MAX_BOUND,
            "window lo ({lo}) must not exceed MAX_BOUND ({})",
            Self::MAX_BOUND
        );
        Window { lo, hi: None }
    }

    pub fn lo(&self) -> u64 {
        self.lo
    }

    /// Upper bound `hi`, or `None` for ∞.
    pub fn hi(&self) -> Option<u64> {
        self.hi
    }

    /// Whether this is the default `ASAP = [0, ∞)` window (an ordinary send).
    pub fn is_untimed(&self) -> bool {
        *self == Window::ASAP
    }
}

impl fmt::Display for Window {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.hi {
            Some(hi) => write!(f, "[{},{}]", self.lo, hi),
            None => write!(f, "[{},∞]", self.lo),
        }
    }
}

/// Predicate of a selective receive. `vals(r)` from Definition 3.1 is the set of values
/// accepted by `test`; `repr` is a human-readable tag used for `Debug`/`Display` and for
/// the canonical key of a graph.
///
/// `repr` identifies the predicate at a given position of a given thread: the runtime
/// tags a receive by its po position, so the same event gets the same `repr` across
/// replays. It is not a global identity - two predicates at the same position on
/// different control-flow branches, or in different threads, can share a `repr` - so
/// callers must not rely on `Pred` equality across threads or branches.
#[derive(Clone)]
pub struct Pred {
    repr: Arc<str>,
    // `Arc` (not `Rc`) keeps `Pred` — and hence `Label` and `ExecutionGraph` — `Send +
    // Sync`, so parallel exploration can hand graph subtrees to worker threads.
    test: Arc<dyn Fn(&str) -> bool + Send + Sync>,
    /// Fast path for equality predicates: `Some(sym)` iff this predicate accepts exactly
    /// the interned payload `sym`. Lets [`test_sym`](Self::test_sym) compare handles
    /// directly, skipping the resolve-and-run-closure step. `None` for a general predicate.
    eq_target: Option<Val>,
}

impl Pred {
    pub fn new(
        repr: impl Into<String>,
        test: impl Fn(&str) -> bool + Send + Sync + 'static,
    ) -> Self {
        Pred {
            repr: Arc::from(repr.into()),
            test: Arc::new(test),
            eq_target: None,
        }
    }

    /// Predicate `true`: accepts any message (the default `recv()`).
    pub fn any() -> Self {
        Pred::new("true", |_| true)
    }

    /// Predicate `x == v`. Records the interned target so [`test_sym`](Self::test_sym) can
    /// match by handle without resolving.
    pub fn eq(v: impl Into<String>) -> Self {
        let v = v.into();
        let sym = crate::intern::intern(&v);
        let mut p = Pred::new(format!("={v}"), move |x| x == v);
        p.eq_target = Some(sym);
        p
    }

    /// Whether `v` satisfies the predicate, i.e. `v` is in `vals(r)`.
    pub fn test(&self, v: &str) -> bool {
        (self.test)(v)
    }

    /// Whether the interned payload `v` satisfies the predicate. Equality predicates match
    /// by handle (no resolve); a general predicate resolves `v` and runs its closure.
    pub fn test_sym(&self, v: Val) -> bool {
        match self.eq_target {
            Some(t) => v == t,
            None => (self.test)(crate::intern::resolve(v)),
        }
    }

    pub fn repr(&self) -> &str {
        &self.repr
    }
}

impl fmt::Debug for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "λx:{}", self.repr)
    }
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.repr)
    }
}

/// Two predicates are equal when their tags match; enough to tell events apart.
impl PartialEq for Pred {
    fn eq(&self, other: &Self) -> bool {
        self.repr == other.repr
    }
}
impl Eq for Pred {}

/// Event label (Definition 3.1). Blocking is scheduler state, not a graph event, so it
/// has no label here. `Nondet` (ND) carries only the option set `S`; the value it
/// resolved to is a separate graph annotation (`graph::ExecutionGraph::nd`), exactly as
/// a receive's read value is its rf edge rather than part of its label.
///
/// The heap-carrying variants (`Recv`/`Nondet`/`Error`) hold their payload behind an
/// `Arc`, so cloning a `Label` shares that payload. Labels are immutable once created, so
/// the sharing is sound.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Label {
    Send {
        model: Model,
        dst: Tid,
        val: Val,
        /// Delivery window (Definition of the time extension). An ordinary `send` carries
        /// [`Window::ASAP`] `= [0, ∞)`, which keeps its label/key byte-identical to the
        /// untimed format.
        window: Window,
    },
    Recv {
        pred: Arc<Pred>,
        blocking: bool,
    },
    /// Data non-determinism ND (Algorithm 1, lines 6 and 19). `set` is the finite option
    /// set `S`, kept sorted and deduplicated so `min(S) = set[0]` and enumeration is
    /// deterministic.
    Nondet {
        set: Arc<[Val]>,
    },
    Error {
        msg: Arc<str>,
    },
}

impl Label {
    pub fn send(model: Model, dst: Tid, val: impl Into<Val>) -> Self {
        Label::Send {
            model,
            dst,
            val: val.into(),
            window: Window::ASAP,
        }
    }

    /// Like [`send`](Self::send) but with an explicit delivery [`Window`]. `send(m, d, v)`
    /// is exactly `send_within(m, d, v, Window::ASAP)`.
    pub fn send_within(model: Model, dst: Tid, val: impl Into<Val>, window: Window) -> Self {
        Label::Send {
            model,
            dst,
            val: val.into(),
            window,
        }
    }

    /// Blocking receive: waits for a matching message.
    pub fn recv(pred: Pred) -> Self {
        Label::Recv {
            pred: Arc::new(pred),
            blocking: true,
        }
    }

    /// Non-blocking receive: may read nothing (a timeout).
    pub fn recv_nb(pred: Pred) -> Self {
        Label::Recv {
            pred: Arc::new(pred),
            blocking: false,
        }
    }

    /// Non-deterministic choice ND over the finite option set `set`. Values are sorted
    /// and deduplicated (String order), so `min(S) = set[0]` (Algorithm 1, line 19) and
    /// enumeration is deterministic (line 6).
    pub fn nondet(set: impl IntoIterator<Item = impl Into<Val>>) -> Self {
        let mut set: Vec<Val> = set.into_iter().map(Into::into).collect();
        // Sort by the resolved string, never by `Sym` id (nondeterministic): this is what
        // makes `min(S) = set[0]` canonical and enumeration order stable across runs and
        // workers. `dedup` then drops repeats (equal strings share a `Sym`, so they are
        // adjacent after the sort).
        set.sort_by(|a, b| crate::intern::resolve(*a).cmp(crate::intern::resolve(*b)));
        set.dedup();
        debug_assert!(!set.is_empty(), "nondet option set must be non-empty");
        Label::Nondet {
            set: Arc::from(set),
        }
    }

    pub fn error(msg: impl Into<String>) -> Self {
        Label::Error {
            msg: Arc::from(msg.into()),
        }
    }

    pub fn is_send(&self) -> bool {
        matches!(self, Label::Send { .. })
    }
    pub fn is_recv(&self) -> bool {
        matches!(self, Label::Recv { .. })
    }
    pub fn is_nondet(&self) -> bool {
        matches!(self, Label::Nondet { .. })
    }
    pub fn is_error(&self) -> bool {
        matches!(self, Label::Error { .. })
    }

    pub fn model(&self) -> Option<Model> {
        match self {
            Label::Send { model, .. } => Some(*model),
            _ => None,
        }
    }
    pub fn dst(&self) -> Option<Tid> {
        match self {
            Label::Send { dst, .. } => Some(*dst),
            _ => None,
        }
    }
    /// A send's delivery [`Window`] (`None` for non-sends). An ordinary send carries
    /// [`Window::ASAP`].
    pub fn window(&self) -> Option<Window> {
        match self {
            Label::Send { window, .. } => Some(*window),
            _ => None,
        }
    }
    /// A send's payload resolved to its bytes. `None` for non-sends. Prefer
    /// [`payload`](Self::payload) when the interned handle suffices (no resolve).
    pub fn val(&self) -> Option<&'static str> {
        match self {
            Label::Send { val, .. } => Some(crate::intern::resolve(*val)),
            _ => None,
        }
    }
    /// A send's payload as the stored (interned, `Copy`) [`Val`]. `None` for non-sends.
    /// Use [`val`](Self::val) when the bytes are needed.
    pub fn payload(&self) -> Option<Val> {
        match self {
            Label::Send { val, .. } => Some(*val),
            _ => None,
        }
    }
    pub fn pred(&self) -> Option<&Pred> {
        match self {
            Label::Recv { pred, .. } => Some(&**pred),
            _ => None,
        }
    }
    pub fn blocking(&self) -> Option<bool> {
        match self {
            Label::Recv { blocking, .. } => Some(*blocking),
            _ => None,
        }
    }
    /// The option set `S` of a nondet label (`None` for any other label). The value the
    /// event resolved to is not here; it is the graph's `nd` annotation.
    pub fn nd_set(&self) -> Option<&[Val]> {
        match self {
            Label::Nondet { set } => Some(&**set),
            _ => None,
        }
    }
}

/// Serial number (t, i) of an event (Definition 3.1). The derived `Ord` is
/// lexicographic on `(tid, idx)`, exactly the tid-then-index order the consistency
/// tiebreaker uses to break ties, so `EventId`s can be sorted directly.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct EventId {
    pub tid: Tid,
    pub idx: usize,
}

impl EventId {
    pub fn new(tid: Tid, idx: usize) -> Self {
        EventId { tid, idx }
    }
}

impl fmt::Display for EventId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "⟨{},{}⟩", self.tid, self.idx)
    }
}

/// An event as an owned `(id, label)` pair. The graph stores labels positionally,
/// but this struct is convenient at the runtime/explorer boundary.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Event {
    pub id: EventId,
    pub label: Label,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicates() {
        assert!(Pred::any().test("anything"));
        assert!(Pred::eq("42").test("42"));
        assert!(!Pred::eq("42").test("7"));
        assert_eq!(Pred::eq("42").repr(), "=42");
        assert_eq!(Pred::any().repr(), "true");
    }

    #[test]
    fn label_projections() {
        let s = Label::send(Model::P2p, 3, "1");
        assert!(s.is_send());
        assert_eq!(s.model(), Some(Model::P2p));
        assert_eq!(s.dst(), Some(3));
        assert_eq!(s.val(), Some("1"));
        assert_eq!(s.pred(), None);

        let r = Label::recv(Pred::any());
        assert!(r.is_recv());
        assert_eq!(r.blocking(), Some(true));
        assert_eq!(r.model(), None);
        assert!(r.pred().is_some());
    }

    #[test]
    fn nondet_label_is_sorted_and_deduped() {
        // Out-of-order, duplicated input -> sorted, unique option set with min(S) first.
        let nd = Label::nondet(["2", "0", "1", "0"]);
        assert!(nd.is_nondet());
        let want: [Val; 3] = ["0".into(), "1".into(), "2".into()];
        assert_eq!(nd.nd_set(), Some(&want[..]));
        // Not confused with other projections.
        assert_eq!(nd.val(), None);
        assert_eq!(nd.model(), None);
        assert_eq!(nd.pred(), None);
    }

    #[test]
    fn event_id_orders_by_tid_then_idx() {
        assert!(EventId::new(0, 5) < EventId::new(1, 0));
        assert!(EventId::new(1, 0) < EventId::new(1, 1));
    }

    #[test]
    fn window_accessors_and_display() {
        let w = Window::new(10, 20);
        assert_eq!(w.lo(), 10);
        assert_eq!(w.hi(), Some(20));
        assert!(!w.is_untimed());
        assert_eq!(w.to_string(), "[10,20]");

        let inf = Window::at_least(10);
        assert_eq!(inf.lo(), 10);
        assert_eq!(inf.hi(), None);
        assert!(!inf.is_untimed());
        assert_eq!(inf.to_string(), "[10,∞]");

        // ASAP = [0, ∞) is the one untimed window; at_least(0) equals it.
        assert!(Window::ASAP.is_untimed());
        assert_eq!(Window::at_least(0), Window::ASAP);
        assert_eq!(Window::ASAP.to_string(), "[0,∞]");
    }

    #[test]
    #[should_panic(expected = "must not exceed hi")]
    fn window_new_rejects_lo_gt_hi() {
        let _ = Window::new(20, 10);
    }

    #[test]
    #[should_panic(expected = "must not exceed MAX_BOUND")]
    fn window_new_rejects_hi_over_max_bound() {
        let _ = Window::new(0, Window::MAX_BOUND + 1);
    }

    #[test]
    #[should_panic(expected = "must not exceed MAX_BOUND")]
    fn window_at_least_rejects_lo_over_max_bound() {
        let _ = Window::at_least(Window::MAX_BOUND + 1);
    }

    #[test]
    fn send_carries_asap_and_send_within_carries_window() {
        // Plain send keeps the default (untimed) window.
        let s = Label::send(Model::P2p, 3, "1");
        assert_eq!(s.window(), Some(Window::ASAP));

        // send_within carries the given window; window() is None for non-sends.
        let w = Window::new(10, 20);
        let t = Label::send_within(Model::P2p, 3, "1", w);
        assert_eq!(t.window(), Some(w));
        assert_eq!(Label::recv(Pred::any()).window(), None);
    }
}
