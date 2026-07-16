//! Graph-level tests: add / set_rf / restrict + re-stamping, porf BFS, canonical_key.

use std::collections::BTreeSet;

use must::event::{EventId, Label, Model, Pred};
use must::graph::ExecutionGraph;

fn send(dst: usize, val: &str) -> Label {
    Label::send(Model::P2p, dst, val)
}

#[test]
fn stamps_follow_insertion_order() {
    let mut g = ExecutionGraph::new();
    let a = g.add_event(0, send(1, "a"));
    let b = g.add_event(1, send(0, "b"));
    let c = g.add_event(0, send(1, "c"));
    assert_eq!(g.events_by_stamp(), vec![a, b, c]);
    assert!(g.stamp(a) < g.stamp(b) && g.stamp(b) < g.stamp(c));
}

#[test]
fn restrict_preserves_relative_order_and_compacts_stamps() {
    let mut g = ExecutionGraph::new();
    let a = g.add_event(0, send(1, "a")); // stamp 0
    let _x = g.add_event(1, send(0, "x")); // stamp 1, dropped
    let b = g.add_event(0, send(1, "b")); // stamp 2
    let _y = g.add_event(2, send(0, "y")); // stamp 3, dropped
    let c = g.add_event(0, send(1, "c")); // stamp 4

    let keep: BTreeSet<EventId> = [a, b, c].into_iter().collect();
    let h = g.restrict(&keep);

    // Only thread 0 survives, with idx preserved.
    assert_eq!(h.thread_len(0), 3);
    assert_eq!(h.thread_len(1), 0);
    assert_eq!(h.thread_len(2), 0);
    // Old stamps 0,2,4 become 0,1,2 in the same relative order.
    assert_eq!(h.stamp(a), 0);
    assert_eq!(h.stamp(b), 1);
    assert_eq!(h.stamp(c), 2);
    assert_eq!(h.events_by_stamp(), vec![a, b, c]);
}

#[test]
fn restrict_normalizes_dangling_rf_to_bottom() {
    let mut g = ExecutionGraph::new();
    let s = g.add_event(0, send(1, "1")); // stamp 0
    let r = g.add_event(1, Label::recv(Pred::any())); // stamp 1
    g.set_rf(r, Some(s));

    // Keep the receive but drop its source send.
    let keep: BTreeSet<EventId> = [r].into_iter().collect();
    let h = g.restrict(&keep);

    assert_eq!(h.thread_len(0), 0);
    assert_eq!(h.thread_len(1), 1);
    assert!(h.reads_bottom(r)); // dangling rf now reads nothing
}

#[test]
fn restrict_keeps_rf_edge_when_both_endpoints_survive() {
    let mut g = ExecutionGraph::new();
    let s = g.add_event(0, send(1, "1"));
    let r = g.add_event(1, Label::recv(Pred::any()));
    let _dropped = g.add_event(2, send(1, "z"));
    g.set_rf(r, Some(s));

    let keep: BTreeSet<EventId> = [s, r].into_iter().collect();
    let h = g.restrict(&keep);
    assert_eq!(h.reads_from(r), Some(s));
    assert!(h.is_read(s));
    assert!(h.unread_sends().is_empty());
}

#[test]
fn add_event_after_restrict_continues_stamping() {
    let mut g = ExecutionGraph::new();
    let a = g.add_event(0, send(1, "a")); // stamp 0
    let _b = g.add_event(1, send(0, "b")); // stamp 1, dropped
    let c = g.add_event(0, send(1, "c")); // stamp 2

    let keep: BTreeSet<EventId> = [a, c].into_iter().collect();
    let mut h = g.restrict(&keep); // survivors re-stamped to 0, 1

    // The next event must get the next fresh stamp and be maximal under <=_G.
    let d = h.add_event(1, send(0, "d"));
    assert_eq!(h.stamp(d), 2);
    assert_eq!(h.events_by_stamp(), vec![a, c, d]);
}

#[test]
fn porf_follows_po_and_rf() {
    let mut g = ExecutionGraph::new();
    // T0: a(S) -> b(S)   T1: c(R reads a) -> d(S)
    let a = g.add_event(0, send(1, "a"));
    let _b = g.add_event(0, send(1, "b"));
    let c = g.add_event(1, Label::recv(Pred::any()));
    let d = g.add_event(1, send(0, "d"));
    g.set_rf(c, Some(a));

    // po within a thread.
    assert!(g.porf_reaches(a, _b));
    assert!(!g.porf_reaches(_b, a));
    // rf edge a -> c.
    assert!(g.porf_reaches(a, c));
    // transitivity a ->rf c ->po d.
    assert!(g.porf_reaches(a, d));
    assert_eq!(g.porf_prefix(d), [a, c].into_iter().collect());
    // no path the other way.
    assert!(!g.porf_reaches(d, a));
}

#[test]
fn canonical_key_ignores_insertion_order_but_tracks_rf() {
    // Same events and rf, different insertion order -> same key.
    let mut g1 = ExecutionGraph::new();
    let s1 = g1.add_event(0, send(1, "1"));
    let r1 = g1.add_event(1, Label::recv(Pred::any()));
    g1.set_rf(r1, Some(s1));

    let mut g2 = ExecutionGraph::new();
    let r2 = g2.add_event(1, Label::recv(Pred::any()));
    let s2 = g2.add_event(0, send(1, "1"));
    g2.set_rf(r2, Some(s2));

    assert_eq!(g1.canonical_key(), g2.canonical_key());

    // Different rf -> different key.
    let mut g3 = ExecutionGraph::new();
    let a = g3.add_event(0, send(1, "1"));
    let _b = g3.add_event(0, send(1, "2"));
    let r = g3.add_event(1, Label::recv(Pred::any()));
    g3.set_rf(r, Some(a));
    let key_reads_a = g3.canonical_key();
    g3.set_rf(r, Some(_b));
    assert_ne!(key_reads_a, g3.canonical_key());
}

#[test]
fn canonical_key_ignores_empty_thread_slots() {
    // A restrict can leave an empty thread slot behind (e.g. a backward revisit
    // deleting a thread's only event); the key must match the same graph reached
    // without that slot ever existing.
    let mut g1 = ExecutionGraph::new();
    let s = g1.add_event(0, send(1, "1"));
    let _x = g1.add_event(2, send(0, "x"));
    let keep: BTreeSet<EventId> = [s].into_iter().collect();
    let h = g1.restrict(&keep); // thread 2 becomes an empty slot

    let mut g2 = ExecutionGraph::new();
    let _s2 = g2.add_event(0, send(1, "1"));

    assert_eq!(h.canonical_key(), g2.canonical_key());
}

#[test]
fn canonical_key_does_not_collide_on_tricky_vals() {
    // A single send whose value mimics the printed form of two labels must not
    // collide with an actual pair of sends (length prefix disambiguates).
    let mut g1 = ExecutionGraph::new();
    g1.add_event(0, send(1, "a) Sp2p(1,1:b"));

    let mut g2 = ExecutionGraph::new();
    g2.add_event(0, send(1, "a"));
    g2.add_event(0, send(1, "b"));

    assert_ne!(g1.canonical_key(), g2.canonical_key());
}
