//! Events and labels of the execution graph.

use std::fmt;
use std::sync::Arc;

/// Thread identifier. Threads are numbered `0..N`.
pub type Tid = usize;

/// Message payload: an interned [`Sym`](crate::intern::Sym), a 4-byte `Copy` handle for a
/// string. Build one from a `&str`/`String` via `.into()`; recover the bytes with
/// [`intern::resolve`](crate::intern::resolve). See [`crate::intern`] for the determinism
/// contract.
pub type Val = crate::intern::Sym;

/// Communication model attached to every `send`. Receives carry no model; only sends do.
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

/// Predicate of a selective receive: `test` decides which payloads it accepts, and `repr`
/// is a human-readable tag used for `Debug`/`Display` and the graph's canonical key.
///
/// `repr` tags a receive by its program-order position, so the same event gets the same
/// `repr` across replays. It is not a global identity: two predicates at the same position
/// on different branches or threads can share a `repr`, so never rely on `Pred` equality
/// across threads or branches.
#[derive(Clone)]
pub struct Pred {
    repr: Arc<str>,
    // `Arc` (not `Rc`) keeps `Pred` — and hence `Label` and `ExecutionGraph` — `Send +
    // Sync`, so parallel exploration can hand graph subtrees to worker threads.
    test: Arc<dyn Fn(&str) -> bool + Send + Sync>,
    /// Fast path for equality predicates: `Some(sym)` iff this predicate accepts exactly the
    /// interned payload `sym`, so [`test_sym`](Self::test_sym) can compare handles directly
    /// without resolving. `None` for a general predicate.
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

    /// Whether `v` satisfies the predicate.
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

/// Event label. Blocking is scheduler state, not a graph event, so it has no label here.
/// `Nondet` carries only the option set; the value it resolved to is a separate graph
/// annotation, just as a receive's read value is its rf edge rather than part of its label.
///
/// The heap-carrying variants hold their payload behind an `Arc`, so cloning a `Label`
/// shares it; labels are immutable, so the sharing is sound.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Label {
    Send {
        model: Model,
        dst: Tid,
        val: Val,
    },
    Recv {
        pred: Arc<Pred>,
        blocking: bool,
    },
    /// Data non-determinism: `set` is the finite option set, kept sorted and deduplicated
    /// so the minimum is `set[0]` and enumeration is deterministic.
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

    /// Non-deterministic choice over the finite option set `set` (sorted and deduplicated).
    pub fn nondet(set: impl IntoIterator<Item = impl Into<Val>>) -> Self {
        let mut set: Vec<Val> = set.into_iter().map(Into::into).collect();
        // Order by the resolved string, never by `Sym` id (which varies between runs), so the
        // minimum and the enumeration order stay stable across runs and workers.
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
    /// The option set of a nondet label (`None` for any other label). The value it resolved
    /// to is not here; that is the graph's `nd` annotation.
    pub fn nd_set(&self) -> Option<&[Val]> {
        match self {
            Label::Nondet { set } => Some(&**set),
            _ => None,
        }
    }
}

/// Serial number of an event. The derived `Ord` is lexicographic on `(tid, idx)`, which is
/// exactly the order the consistency tiebreaker uses, so `EventId`s can be sorted directly.
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
}
