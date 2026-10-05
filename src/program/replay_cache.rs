use std::cell::RefCell;
use std::mem::size_of;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crate::{Label, Program, ProgramCursor, ThreadNext, Tid, TraceLabel, Val};

// Each explorer worker constructs its own System and cache. Keys retain the full
// local event trace: receive outcomes alone would lose positions between sends.
pub(crate) struct CachedProgram<P: Program> {
    system: P,
    owner: Option<u64>,
    cache: RefCell<ReplayCache>,
    enabled: bool,
}

#[derive(Default)]
struct CachedThread {
    tid: Tid,
    next: Option<ThreadNext>,
    labels: Option<Arc<[TraceLabel]>>,
    edge: Option<usize>,
    incoming: Option<Val>,
}

struct TraceEdge {
    value: Option<Val>,
    child: usize,
    sibling: Option<usize>,
}

// Prefix histories share arena nodes. Equality is sufficient: intern IDs never
// determine exploration order, and no payload strings are resolved on lookups.
struct ReplayCache {
    roots: Vec<Option<usize>>,
    recent: RefCell<Vec<Vec<usize>>>,
    nodes: Vec<CachedThread>,
    edges: Vec<TraceEdge>,
    entries: usize,
    epoch: u64,
    cursors_enabled: bool,
    trace_cells: usize,
    bytes: usize,
    max_entries: usize,
    max_trace_cells: usize,
    max_bytes: usize,
}

impl ReplayCache {
    fn find(&self, tid: Tid, trace: &[Option<Val>]) -> Option<usize> {
        let root = *self.roots.get(tid)?.as_ref()?;
        let mut recent = self.recent.borrow_mut();
        if recent.len() <= tid {
            recent.resize_with(tid + 1, Vec::new);
        }
        let path = &mut recent[tid];
        if path.first() != Some(&root) {
            path.clear();
            path.push(root);
        }
        let mut shared = 0;
        while shared < trace.len()
            && shared + 1 < path.len()
            && self.nodes[path[shared + 1]].incoming == trace[shared]
        {
            shared += 1;
        }
        path.truncate(shared + 1);
        let mut node = path[shared];
        for value in &trace[shared..] {
            let mut edge = self.nodes[node].edge;
            node = loop {
                let e = &self.edges[edge?];
                if e.value == *value {
                    break e.child;
                }
                edge = e.sibling;
            };
            path.push(node);
        }
        Some(node)
    }

    fn get(&self, tid: Tid, trace: &[Option<Val>]) -> Option<&CachedThread> {
        self.find(tid, trace).map(|node| &self.nodes[node])
    }

    fn missing_nodes(&self, tid: Tid, trace: &[Option<Val>]) -> usize {
        let Some(mut node) = self.roots.get(tid).copied().flatten() else {
            return trace.len() + 1;
        };
        for (position, value) in trace.iter().enumerate() {
            let mut edge = self.nodes[node].edge;
            loop {
                let Some(index) = edge else {
                    return trace.len() - position;
                };
                let e = &self.edges[index];
                if e.value == *value {
                    node = e.child;
                    break;
                }
                edge = e.sibling;
            }
        }
        0
    }

    fn insert_path(&mut self, tid: Tid, trace: &[Option<Val>]) -> usize {
        if self.roots.len() <= tid {
            self.roots.resize(tid + 1, None);
        }
        let mut node = match self.roots[tid] {
            Some(node) => node,
            None => {
                let node = self.nodes.len();
                self.nodes.push(CachedThread {
                    tid,
                    ..CachedThread::default()
                });
                self.roots[tid] = Some(node);
                node
            }
        };
        for value in trace {
            let mut edge = self.nodes[node].edge;
            let found = loop {
                let Some(index) = edge else {
                    break None;
                };
                let e = &self.edges[index];
                if e.value == *value {
                    break Some(e.child);
                }
                edge = e.sibling;
            };
            node = if let Some(child) = found {
                child
            } else {
                let child = self.nodes.len();
                self.nodes.push(CachedThread {
                    tid,
                    incoming: *value,
                    ..CachedThread::default()
                });
                let index = self.edges.len();
                self.edges.push(TraceEdge {
                    value: *value,
                    child,
                    sibling: self.nodes[node].edge,
                });
                self.nodes[node].edge = Some(index);
                child
            };
        }
        node
    }

    fn store(
        &mut self,
        tid: Tid,
        trace: &[Option<Val>],
        next: Option<ThreadNext>,
        labels: Option<Arc<[TraceLabel]>>,
    ) -> bool {
        self.store_entry(tid, trace, next, labels, true)
    }

    fn store_entry(
        &mut self,
        tid: Tid,
        trace: &[Option<Val>],
        next: Option<ThreadNext>,
        labels: Option<Arc<[TraceLabel]>>,
        evict: bool,
    ) -> bool {
        let existing = self.get(tid, trace);
        let new_entry = existing.is_none_or(|entry| entry.next.is_none() && entry.labels.is_none());
        let next = next.filter(|_| existing.is_none_or(|entry| entry.next.is_none()));
        let labels = labels.filter(|_| existing.is_none_or(|entry| entry.labels.is_none()));
        if next.is_none() && labels.is_none() {
            return true;
        }
        let missing = self.missing_nodes(tid, trace);
        // Account physical prefix edges, rather than repeatedly charging the
        // shared prefix for every computed history.
        let cells = missing.saturating_sub(usize::from(
            self.roots.get(tid).copied().flatten().is_none(),
        ));
        let mut bytes = missing.saturating_mul(size_of::<CachedThread>() + size_of::<TraceEdge>());
        if let Some(ThreadNext::Next(label)) = &next {
            bytes = bytes.saturating_add(match label {
                Label::Nondet { set } => std::mem::size_of_val(set.as_ref()),
                Label::Error { msg } => msg.len(),
                Label::Recv { pred, .. } => pred.repr().len() + size_of::<crate::Pred>(),
                Label::Send { .. } => 0,
            });
        }
        if let Some(labels) = &labels {
            bytes = bytes.saturating_add(labels.len().saturating_mul(size_of::<TraceLabel>()));
        }
        if (new_entry && self.entries >= self.max_entries)
            || self.trace_cells.saturating_add(cells) > self.max_trace_cells
            || self.bytes.saturating_add(bytes) > self.max_bytes
        {
            if evict && self.entries != 0 {
                self.roots.fill(None);
                self.recent.borrow_mut().clear();
                self.nodes.clear();
                self.edges.clear();
                self.entries = 0;
                self.epoch = self.epoch.wrapping_add(1);
                if self.epoch == 0 {
                    self.cursors_enabled = false;
                }
                self.trace_cells = 0;
                self.bytes = 0;
                return self.store_entry(tid, trace, next, labels, evict);
            }
            return false;
        }
        self.trace_cells += cells;
        self.bytes += bytes;
        self.entries += usize::from(new_entry);
        let node = self.insert_path(tid, trace);
        let entry = &mut self.nodes[node];
        if let Some(next) = next {
            entry.next = Some(next);
        }
        if let Some(labels) = labels {
            entry.labels = Some(labels);
        }
        true
    }
}

static CACHE_OWNERS: AtomicU64 = AtomicU64::new(1);

impl<P: Program> CachedProgram<P> {
    fn cursor_for(&self, cache: &ReplayCache, node: usize) -> Option<ProgramCursor> {
        if !cache.cursors_enabled {
            return None;
        }
        Some(ProgramCursor::new([
            self.owner?,
            cache.epoch,
            u64::try_from(node).ok()?,
        ]))
    }

    pub fn new(system: P) -> Self {
        Self::with_limits(system, 100_000, 250_000, 8 * 1024 * 1024)
    }

    fn prefix_node(cache: &ReplayCache, tid: Tid, token: u64) -> Option<usize> {
        if !cache.cursors_enabled || cache.epoch > u32::MAX as u64 {
            return None;
        }
        let node = if token == 0 {
            cache.roots.get(tid).copied().flatten()?
        } else {
            if token >> 32 != cache.epoch {
                return None;
            }
            usize::try_from((token as u32).checked_sub(1)?).ok()?
        };
        cache
            .nodes
            .get(node)
            .filter(|entry| entry.tid == tid && entry.next.is_some())?;
        Some(node)
    }

    fn with_limits(
        mut system: P,
        max_entries: usize,
        max_trace_cells: usize,
        max_bytes: usize,
    ) -> Self {
        let enabled = system.supports_replay_cache();
        if enabled {
            system.prepare_exploration();
        }
        Self {
            system,
            enabled,
            owner: CACHE_OWNERS
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                .ok(),
            cache: RefCell::new(ReplayCache {
                roots: Vec::new(),
                recent: RefCell::new(Vec::new()),
                nodes: Vec::new(),
                edges: Vec::new(),
                entries: 0,
                epoch: 0,
                cursors_enabled: true,
                trace_cells: 0,
                bytes: 0,
                max_entries,
                max_trace_cells,
                max_bytes,
            }),
        }
    }
}

impl<P: Program> Program for CachedProgram<P> {
    #[inline]
    fn prefix_namespace(&self) -> Option<u64> {
        if !self.enabled {
            return self.system.prefix_namespace();
        }
        self.owner
    }

    #[inline]
    fn persist_cursor(&self, tid: Tid, cursor: ProgramCursor) -> Option<u64> {
        if !self.enabled {
            return self.system.persist_cursor(tid, cursor);
        }
        let [owner, epoch, node] = cursor.words();
        let cache = self.cache.borrow();
        if self.owner != Some(owner) || !cache.cursors_enabled || epoch != cache.epoch {
            return None;
        }
        let epoch = u32::try_from(epoch).ok()?;
        let encoded_node = u32::try_from(node).ok()?.checked_add(1)?;
        cache
            .nodes
            .get(usize::try_from(node).ok()?)
            .filter(|entry| entry.tid == tid && entry.next.is_some())?;
        Some((u64::from(epoch) << 32) | u64::from(encoded_node))
    }

    #[inline]
    fn next_thread_at_prefix(&self, tid: Tid, token: u64) -> Option<(ThreadNext, ProgramCursor)> {
        if !self.enabled {
            return self.system.next_thread_at_prefix(tid, token);
        }
        let cache = self.cache.borrow();
        let node = Self::prefix_node(&cache, tid, token)?;
        Some((
            cache.nodes[node].next.clone()?,
            self.cursor_for(&cache, node)?,
        ))
    }

    fn labels_at_prefixes(&self, tokens: &[u64]) -> Option<Vec<TraceLabel>> {
        if !self.enabled {
            return self.system.labels_at_prefixes(tokens);
        }
        if tokens.len() != self.num_threads() {
            return None;
        }
        let cache = self.cache.borrow();
        let rows = tokens
            .iter()
            .enumerate()
            .map(|(tid, &token)| {
                let node = Self::prefix_node(&cache, tid, token)?;
                cache.nodes[node].labels.as_deref()
            })
            .collect::<Option<Vec<_>>>()?;
        let mut labels = Vec::with_capacity(rows.iter().map(|row| row.len()).sum());
        for row in rows {
            labels.extend(row.iter().cloned());
        }
        Some(labels)
    }

    fn num_threads(&self) -> usize {
        self.system.num_threads()
    }

    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        if !self.enabled {
            return self.system.next(traces);
        }
        debug_assert_eq!(traces.len(), self.num_threads());
        traces
            .iter()
            .enumerate()
            .map(|(tid, trace)| self.next_thread(tid, trace))
            .collect()
    }

    fn next_thread(&self, tid: Tid, trace: &[Option<Val>]) -> ThreadNext {
        if !self.enabled {
            return self.system.next_thread(tid, trace);
        }
        let cached = self
            .cache
            .borrow()
            .get(tid, trace)
            .and_then(|entry| entry.next.clone());
        if let Some(next) = cached {
            return next;
        }
        // One poll extracts the deterministic send-only suffix up to its next
        // choice. Each answer is cached under its exact full per-event prefix;
        // graph construction still commits one event at a time.
        let Some(batch) = self.system.replay_batch(tid, trace) else {
            return self.system.next_thread(tid, trace);
        };
        let next = batch
            .steps
            .first()
            .expect("replay always has a next outcome")
            .clone();
        let mut prefix = trace.to_vec();
        let mut cache = self.cache.borrow_mut();
        let mut label_end = 0;
        let mut prefix_labels: Arc<[TraceLabel]> = Arc::from([]);
        // Keep prefetch work bounded even for a long send-only process. Refused
        // entries remain ordinary cache misses and use the same replay fallback.
        for (offset, step) in batch.steps.into_iter().take(64).enumerate() {
            if offset != 0 {
                prefix.push(None);
            }
            let end = batch
                .labels
                .partition_point(|label| label.position <= prefix.len());
            if end != label_end {
                prefix_labels = Arc::from(&batch.labels[..end]);
                label_end = end;
            }
            // Speculative successors never evict the actually requested entry.
            let epoch = cache.epoch;
            if !cache.store_entry(
                tid,
                &prefix,
                Some(step),
                Some(prefix_labels.clone()),
                offset == 0,
            ) {
                break;
            }
            // On eviction, keep the new epoch focused on this requested result.
            if cache.epoch != epoch {
                break;
            }
        }
        drop(cache);
        next
    }

    fn next_thread_cursor(
        &self,
        tid: Tid,
        trace: &[Option<Val>],
    ) -> (ThreadNext, Option<ProgramCursor>) {
        if !self.enabled {
            return self.system.next_thread_cursor(tid, trace);
        }
        {
            let cache = self.cache.borrow();
            if let Some(node) = cache.find(tid, trace) {
                if let Some(next) = &cache.nodes[node].next {
                    return (next.clone(), self.cursor_for(&cache, node));
                }
            }
        }
        let next = self.next_thread(tid, trace);
        let cache = self.cache.borrow();
        let cursor = cache
            .find(tid, trace)
            .and_then(|node| self.cursor_for(&cache, node));
        (next, cursor)
    }

    #[inline]
    fn advance_thread(
        &self,
        tid: Tid,
        cursor: ProgramCursor,
        entry: Option<Val>,
    ) -> Option<(ThreadNext, ProgramCursor)> {
        if !self.enabled {
            return self.system.advance_thread(tid, cursor, entry);
        }
        let [owner, epoch, slot] = cursor.words();
        let cache = self.cache.borrow();
        if self.owner != Some(owner) || !cache.cursors_enabled || cache.epoch != epoch {
            return None;
        }
        let node = usize::try_from(slot).ok()?;
        let parent = cache.nodes.get(node)?;
        if parent.tid != tid || parent.next.is_none() {
            return None;
        }
        let mut edge = parent.edge;
        while let Some(index) = edge {
            let candidate = &cache.edges[index];
            if candidate.value == entry {
                let child = candidate.child;
                let next = cache.nodes[child].next.clone()?;
                return Some((next, self.cursor_for(&cache, child)?));
            }
            edge = candidate.sibling;
        }
        None
    }

    fn labels(&self, traces: &[Vec<Option<Val>>]) -> Vec<TraceLabel> {
        if !self.enabled {
            return self.system.labels(traces);
        }
        debug_assert_eq!(traces.len(), self.num_threads());
        let cached = {
            let cache = self.cache.borrow();
            traces
                .iter()
                .enumerate()
                .map(|(tid, trace)| cache.get(tid, trace).and_then(|entry| entry.labels.clone()))
                .collect::<Option<Vec<_>>>()
        };
        if let Some(labels) = cached {
            let mut combined = Vec::with_capacity(labels.iter().map(|row| row.len()).sum());
            for row in labels {
                combined.extend(row.iter().cloned());
            }
            return combined;
        }
        // Replay the actual full traces once. Artificial empty traces for other
        // threads would reconstruct the wrong prefix annotations on early errors.
        let labels = self.system.labels(traces);
        let mut by_thread = vec![Vec::new(); self.num_threads()];
        for label in &labels {
            by_thread[label.tid].push(label.clone());
        }
        let mut cache = self.cache.borrow_mut();
        for (tid, thread_labels) in by_thread.into_iter().enumerate() {
            // Empty labels are cached too: None means not yet computed.
            cache.store(tid, &traces[tid], None, Some(thread_labels.into()));
        }
        labels
    }

    fn possible_future(&self, tid: Tid, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        self.system.possible_future(tid, trace)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::rc::Rc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    #[derive(Default)]
    struct Record {
        terminals: Mutex<Vec<String>>,
        errors: AtomicUsize,
        cuts: AtomicUsize,
        events: AtomicUsize,
    }

    impl crate::Observer for Record {
        fn on_execution(&self, execution: &crate::Execution, kind: crate::ExecutionKind) {
            if kind == crate::ExecutionKind::Error {
                self.errors.fetch_add(1, Ordering::Relaxed);
            }
            self.terminals.lock().unwrap().push(format!(
                "{kind:?}|{}|{:?}",
                execution.canonical_key(),
                execution.labels()
            ));
        }

        fn on_send_limit(&self, _: &crate::ExecutionGraph, _: usize) {
            self.cuts.fetch_add(1, Ordering::Relaxed);
        }

        fn on_event_added(&self, _: &crate::ExecutionGraph, _: crate::EventId) {
            self.events.fetch_add(1, Ordering::Relaxed);
        }
    }

    fn branching() -> crate::System {
        let mut system = crate::System::new();
        system.add(|ctx| async move {
            ctx.insert_label("sender:start");
            let value = ctx.nondet(["good", "bad"]).await;
            ctx.send(2, value, crate::Model::Asyn);
            ctx.insert_label("sender:sent");
            ctx.send(2, "tail", crate::Model::Asyn);
        });
        system.add(|ctx| async move {
            ctx.send(2, "other", crate::Model::Asyn);
        });
        system.add(|ctx| async move {
            ctx.insert_label("receiver:start");
            for _ in 0..3 {
                let value = ctx.recv_any().await;
                ctx.insert_label(format!("received:{value}"));
                ctx.assert_that(value != "bad", "bad branch");
            }
        });
        system
    }

    struct Uncached(crate::System);

    impl Program for Uncached {
        fn num_threads(&self) -> usize {
            self.0.num_threads()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.0.next(traces)
        }
        fn next_thread(&self, tid: Tid, trace: &[Option<Val>]) -> ThreadNext {
            self.0.next_thread(tid, trace)
        }
        fn labels(&self, traces: &[Vec<Option<Val>>]) -> Vec<TraceLabel> {
            self.0.labels(traces)
        }
        fn possible_future(&self, tid: Tid, trace: &[Option<Val>]) -> Option<Vec<Label>> {
            self.0.possible_future(tid, trace)
        }
    }

    fn record<P: Program>(
        make: impl Fn() -> P + Sync,
        max_sends: usize,
        threads: usize,
    ) -> (Vec<String>, usize, usize, usize) {
        let observer = Record::default();
        crate::explore(
            make,
            &observer,
            crate::Config::default()
                .with_threads(threads)
                .with_max_sends(max_sends)
                .collect_errors(),
        );
        let mut terminals = observer.terminals.into_inner().unwrap();
        terminals.sort();
        (
            terminals,
            observer.errors.into_inner(),
            observer.cuts.into_inner(),
            observer.events.into_inner(),
        )
    }

    #[test]
    fn cached_replay_preserves_graphs_labels_errors_and_send_cuts() {
        for max_sends in [2, 3] {
            let expected = record(|| Uncached(branching()), max_sends, 1);
            assert_eq!(expected, record(branching, max_sends, 1));
            assert_eq!(
                expected,
                record(|| CachedProgram::new(branching()), max_sends, 1)
            );
            let parallel = record(|| Uncached(branching()), max_sends, 4);
            assert_eq!(parallel, record(branching, max_sends, 4));
            assert_eq!(
                parallel,
                record(|| CachedProgram::new(branching()), max_sends, 4)
            );
            // Parallel search must preserve terminals/annotations and outcomes;
            // the number of intermediate additions is not a semantic invariant.
            assert_eq!(
                (&expected.0, expected.1, expected.2),
                (&parallel.0, parallel.1, parallel.2)
            );
            // Zero/oversized limits bypass; a small nonzero cache repeatedly
            // evicts populated epochs. Neither may change exploration results.
            for (entries, cells, bytes) in [
                (0, 100, 10_000),
                (2, 0, 10_000),
                (100, 100, 0),
                (2, 100, 10_000),
            ] {
                assert_eq!(
                    expected,
                    record(
                        || CachedProgram::with_limits(branching(), entries, cells, bytes),
                        max_sends,
                        1
                    )
                );
            }
            if max_sends == 2 {
                assert!(expected.2 > 0);
            } else {
                assert!(expected.1 > 0);
                assert!(!expected.0.is_empty());
            }
        }
    }

    #[test]
    fn labels_use_full_traces_and_cache_empty_results() {
        let polls = Rc::new(Cell::new(0));
        let mut system = crate::System::new();
        for tid in 0..2 {
            let polls = polls.clone();
            system.add(move |ctx| {
                polls.set(polls.get() + 1);
                async move {
                    let value = ctx.recv_any().await;
                    if tid == 1 {
                        ctx.insert_label(format!("seen:{value}"));
                    }
                }
            });
        }
        let system = CachedProgram::new(system);
        let traces = vec![vec![Some("left".into())], vec![Some("right".into())]];
        let labels = system.labels(&traces);
        assert_eq!(labels.len(), 1);
        assert_eq!(crate::intern::resolve(labels[0].value), "seen:right");
        assert_eq!(labels[0].tid, 1);
        assert_eq!(labels[0].position, 1);
        assert_eq!(polls.get(), 2);
        assert_eq!(labels, system.labels(&traces));
        assert_eq!(polls.get(), 2);
        let next = system.next(&traces);
        assert_eq!(polls.get(), 4);
        assert_eq!(next, system.next(&traces));
        assert_eq!(polls.get(), 4);
    }

    #[test]
    fn send_burst_prefetch_reuses_one_body_without_leaking_future_annotations() {
        let polls = Rc::new(Cell::new(0));
        let make = || {
            let polls = polls.clone();
            let mut system = crate::System::new();
            system.add(move |ctx| {
                polls.set(polls.get() + 1);
                async move {
                    ctx.insert_label("before");
                    ctx.send(0, "a", crate::Model::Asyn);
                    ctx.insert_label("after-a");
                    ctx.insert_label("also-after-a");
                    ctx.send(0, "b", crate::Model::Asyn);
                    ctx.insert_label("after-b");
                    let value = ctx.recv_any().await;
                    ctx.insert_label(format!("received:{value}"));
                    ctx.send(0, value, crate::Model::Asyn);
                }
            });
            system
        };
        let cached = CachedProgram::new(make());
        let mut trace = Vec::new();
        for expected in ["a", "b"] {
            let next = cached.next_thread(0, &trace);
            assert_eq!(next.label().unwrap().val(), Some(expected));
            let labels = cached.labels(&[trace.clone()]);
            assert!(labels.iter().all(|label| label.position <= trace.len()));
            trace.push(None);
        }
        assert!(cached.next_thread(0, &trace).label().unwrap().is_recv());
        let labels = cached.labels(&[trace.clone()]);
        assert_eq!(
            labels
                .iter()
                .map(|label| crate::intern::resolve(label.value))
                .collect::<Vec<_>>(),
            ["before", "after-a", "also-after-a", "after-b"]
        );
        assert_eq!(polls.get(), 1);
        trace.push(Some("reply".into()));
        assert_eq!(
            cached.next_thread(0, &trace).label().unwrap().val(),
            Some("reply")
        );
        trace.push(None);
        assert!(cached.next_thread(0, &trace).is_finished());
        assert_eq!(
            cached.labels(&[trace]).last().unwrap().value,
            "received:reply".into()
        );
        assert_eq!(polls.get(), 1);

        // Speculative entries cannot evict the requested prefix in a tiny cache.
        let tiny = CachedProgram::with_limits(make(), 1, 100, 10_000);
        tiny.next_thread(0, &[]);
        let cache = tiny.cache.borrow();
        assert_eq!(cache.entries, 1);
        assert!(cache.get(0, &[]).unwrap().next.is_some());
        assert!(cache.get(0, &[None]).is_none());
        drop(cache);

        // Long deterministic bursts still have bounded cache prefetch work.
        let mut system = crate::System::new();
        system.add(|ctx| async move {
            for _ in 0..100 {
                ctx.send(0, "long", crate::Model::Asyn);
            }
        });
        let bounded = CachedProgram::new(system);
        bounded.next_thread(0, &[]);
        let cache = bounded.cache.borrow();
        assert_eq!(cache.entries, 64);
        assert!(cache.get(0, &[None; 63]).is_some());
        assert!(cache.get(0, &[None; 64]).is_none());
    }

    #[test]
    fn continuation_cursors_validate_ownership_epoch_and_thread() {
        let cached = CachedProgram::new(branching());
        let (first, parent) = cached.next_thread_cursor(0, &[]);
        let parent = parent.unwrap();
        assert!(matches!(first.label().unwrap(), Label::Nondet { .. }));
        let good = Some("good".into());
        assert!(cached.advance_thread(0, parent, good).is_none());
        let (next, child) = cached.next_thread_cursor(0, &[good]);
        let (advanced, cursor) = cached.advance_thread(0, parent, good).unwrap();
        assert_eq!(advanced, next);
        assert_eq!(Some(cursor), child);
        let (tail, tail_cursor) = cached.advance_thread(0, cursor, None).unwrap();
        assert_eq!(tail.label().unwrap().val(), Some("tail"));
        assert!(cached
            .advance_thread(0, tail_cursor, None)
            .unwrap()
            .0
            .is_finished());
        assert!(cached.advance_thread(1, parent, good).is_none());
        let unrelated = CachedProgram::new(branching());
        assert!(unrelated.advance_thread(0, parent, good).is_none());
        let mut forged = parent.words();
        forged[2] = u64::MAX;
        assert!(cached
            .advance_thread(0, ProgramCursor::new(forged), good)
            .is_none());

        let tiny = CachedProgram::with_limits(branching(), 2, 100, 10_000);
        let (_, old) = tiny.next_thread_cursor(0, &[]);
        tiny.next_thread(0, &[good]);
        tiny.next_thread(1, &[]); // Starts a fresh bounded epoch.
        assert!(tiny.advance_thread(0, old.unwrap(), good).is_none());

        let zero = CachedProgram::with_limits(branching(), 0, 100, 10_000);
        assert!(zero.next_thread_cursor(0, &[]).1.is_none());
        // Generation exhaustion disables cursors rather than reusing old handles.
        let exhausted = CachedProgram::with_limits(branching(), 1, 100, 10_000);
        exhausted.next_thread(0, &[]);
        exhausted.cache.borrow_mut().epoch = u64::MAX;
        exhausted.next_thread(1, &[]);
        assert!(!exhausted.cache.borrow().cursors_enabled);
        assert!(exhausted.next_thread_cursor(1, &[]).1.is_none());
    }

    #[test]
    fn persistent_local_prefixes_reuse_existing_nodes_and_preserve_annotations() {
        let system = CachedProgram::new(branching());
        let (_, root) = system.next_thread_cursor(0, &[]);
        let root = root.unwrap();
        let root_token = system.persist_cursor(0, root).unwrap();
        assert_eq!(system.next_thread_at_prefix(0, 0).unwrap().1, root);
        let trace = [Some("good".into())];
        let (next, child) = system.next_thread_cursor(0, &trace);
        let child = child.unwrap();
        let token = system.persist_cursor(0, child).unwrap();
        assert_ne!(root_token, token);
        assert_eq!(
            system.next_thread_at_prefix(0, token).unwrap(),
            (next, child)
        );
        let (_, other) = system.next_thread_cursor(1, &[]);
        let other_token = system.persist_cursor(1, other.unwrap()).unwrap();
        let (_, receiver) = system.next_thread_cursor(2, &[]);
        let receiver_token = system.persist_cursor(2, receiver.unwrap()).unwrap();
        assert_eq!(
            system
                .labels_at_prefixes(&[token, other_token, receiver_token])
                .unwrap(),
            system.labels(&[trace.to_vec(), Vec::new(), Vec::new()])
        );
        assert!(system.next_thread_at_prefix(1, token).is_none());
        assert!(system.persist_cursor(1, child).is_none());
        let foreign = CachedProgram::new(branching());
        assert_ne!(system.prefix_namespace(), foreign.prefix_namespace());
        assert!(foreign.persist_cursor(0, child).is_none());
        assert!(system.next_thread_at_prefix(0, u64::MAX).is_none());
        assert!(system.next_thread_at_prefix(0, 1_u64 << 32).is_none());
        assert!(system.labels_at_prefixes(&[token]).is_none());
    }

    #[test]
    fn persistent_generation_retirement_and_eviction_never_alias_old_nodes() {
        let system = CachedProgram::with_limits(branching(), 2, 100, 10_000);
        let (_, cursor) = system.next_thread_cursor(0, &[]);
        let cursor = cursor.unwrap();
        let token = system.persist_cursor(0, cursor).unwrap();
        system.next_thread(0, &[Some("good".into())]);
        system.next_thread(1, &[]);
        assert!(system.next_thread_at_prefix(0, token).is_none());
        assert!(system.persist_cursor(0, cursor).is_none());
        let (_, latest) = system.next_thread_cursor(1, &[]);
        let latest = latest.unwrap();
        assert_ne!(system.persist_cursor(1, latest).unwrap(), token);
        system.cache.borrow_mut().epoch = u32::MAX as u64 + 1;
        let (_, wide) = system.next_thread_cursor(1, &[]);
        assert!(system.persist_cursor(1, wide.unwrap()).is_none());
        assert!(system.next_thread_at_prefix(1, 0).is_none());
        assert!(system.next_thread_at_prefix(1, token).is_none());
        assert!(system.cache.borrow().cursors_enabled);
    }

    #[test]
    fn trie_shares_prefixes_and_distinguishes_event_positions() {
        let system = CachedProgram::new(branching());
        let good = Some("good".into());
        let bad = Some("bad".into());
        let mut cache = system.cache.borrow_mut();
        for trace in [
            vec![good],
            vec![good, None],
            vec![good, bad],
            vec![None, good],
        ] {
            cache.store(0, &trace, Some(ThreadNext::Finished), None);
        }
        assert_eq!(cache.nodes.len(), 6);
        assert_eq!(cache.edges.len(), 5);
        assert_eq!(cache.entries, 4);
        assert!(cache.get(0, &[good, None]).unwrap().next.is_some());
        assert!(cache.get(0, &[None, good]).unwrap().next.is_some());
        assert!(cache.get(0, &[bad]).is_none());
        assert!(cache.get(1, &[good]).is_none());
        assert!(cache.get(0, &[]).unwrap().next.is_none());
    }

    #[test]
    fn cache_storage_stays_within_all_limits() {
        let system = CachedProgram::with_limits(branching(), 2, 1, 1024);
        system.next_thread(0, &[]);
        system.next_thread(0, &[Some("good".into())]);
        system.next_thread(1, &[]);
        system.next_thread(0, &[Some("good".into()), None]);
        let cache = system.cache.borrow();
        assert!(cache.entries <= 2);
        assert!(cache.trace_cells <= 1);
        assert!(cache.bytes <= 1024);
    }

    #[test]
    fn saturated_cache_starts_a_new_epoch_with_the_current_result() {
        let system = CachedProgram::with_limits(branching(), 2, 100, 10_000);
        system.next_thread(0, &[]);
        system.next_thread(0, &[Some("good".into())]);
        assert_eq!(system.cache.borrow().entries, 2);
        let latest = system.next_thread(1, &[]);
        let cache = system.cache.borrow();
        assert_eq!(cache.entries, 1);
        assert_eq!(cache.trace_cells, 0);
        assert_eq!(cache.get(1, &[]).unwrap().next, Some(latest));
        assert!(!cache.get(0, &[]).is_some());
        assert!(cache.bytes <= 10_000);
    }
}
