//! Bounded proofs that an untimed Asyn suffix only consumes existing messages.
//!
//! With no future sends, each process's remaining inputs are drawn from its own
//! current mailbox. Exhausting every local permutation therefore covers their
//! Cartesian product without constructing all global terminal graphs. No Python
//! state equivalence or inference from a single empty callback is involved.

use std::cell::RefCell;

use crate::{
    EventId, ExecutionGraph, Label, Model, Program, ReceiveTiming, ThreadNext, TraceLabel, Val,
};

/// Work limits for one optional receive-tail proof. Exhaustion keeps ordinary MUST.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReceiveTailBudget {
    /// Total local permutation prefixes inspected across all processes.
    pub max_states: usize,
    /// Maximum current mailbox length at any process. The effective limit is
    /// capped at 64 to bound the proof stack independently of the work budget.
    pub max_pending_per_thread: usize,
}

impl Default for ReceiveTailBudget {
    fn default() -> Self {
        Self {
            max_states: 8192,
            max_pending_per_thread: 8,
        }
    }
}

/// Evidence bound to this exact construction prefix, not a completed execution.
///
/// Every continuation consumes only these pending sends: there are no new sends,
/// errors, nondeterministic choices or annotations. Processes with pending sends
/// continue accepting every payload until their mailbox is drained. The observer
/// must separately prove its property for *every* represented terminal graph.
/// Only the explorer's exhaustive bounded proof can construct this evidence.
#[derive(Debug)]
pub struct ReceiveTailCertificate<'a> {
    graph: &'a ExecutionGraph,
    labels: &'a [TraceLabel],
    pending: Vec<Vec<EventId>>,
    states_checked: usize,
}

impl ReceiveTailCertificate<'_> {
    pub fn graph(&self) -> &ExecutionGraph {
        self.graph
    }
    pub fn labels(&self) -> &[TraceLabel] {
        self.labels
    }
    /// Actual unread send identities, grouped by destination process.
    pub fn pending_sends(&self) -> &[Vec<EventId>] {
        &self.pending
    }
    pub fn states_checked(&self) -> usize {
        self.states_checked
    }
}

const LOCAL_MEMO_SLOTS: usize = 1024;

#[derive(Default)]
struct LocalEntry {
    identity: Option<(u64, u64)>,
    tid: usize,
    hash: u64,
    packets: Vec<(EventId, Val)>,
}

struct LocalMemo {
    entries: [LocalEntry; LOCAL_MEMO_SLOTS],
}

impl Default for LocalMemo {
    fn default() -> Self {
        Self {
            entries: std::array::from_fn(|_| LocalEntry::default()),
        }
    }
}

thread_local! {
    // Only positive *local* no-effect proofs. A prefix token identifies one exact
    // local history (including its annotations), independently of other actors.
    // Direct mapping bounds memory and exact comparisons make hash collisions safe.
    static LOCAL_MEMO: RefCell<LocalMemo> = RefCell::new(LocalMemo::default());
}

fn memo_hash(identity: (u64, u64), tid: usize, packets: &[EventId]) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    for word in [identity.0, identity.1, tid as u64, packets.len() as u64]
        .into_iter()
        .chain(packets.iter().flat_map(|id| [id.tid as u64, id.idx as u64]))
    {
        hash = (hash ^ word).wrapping_mul(0x100000001b3);
    }
    hash
}

impl LocalMemo {
    fn contains(
        &self,
        identity: (u64, u64),
        tid: usize,
        graph: &ExecutionGraph,
        packets: &[EventId],
        hash: u64,
    ) -> bool {
        let entry = &self.entries[hash as usize % LOCAL_MEMO_SLOTS];
        entry.identity == Some(identity)
            && entry.tid == tid
            && entry.hash == hash
            && entry.packets.len() == packets.len()
            && entry
                .packets
                .iter()
                .zip(packets)
                .all(|(&(stored, value), &event)| {
                    stored == event
                        && matches!(graph.label(event), Label::Send { val, .. } if *val == value)
                })
    }

    fn insert(
        &mut self,
        identity: (u64, u64),
        tid: usize,
        graph: &ExecutionGraph,
        packets: &[EventId],
        hash: u64,
    ) {
        let entry = &mut self.entries[hash as usize % LOCAL_MEMO_SLOTS];
        entry.identity = Some(identity);
        entry.tid = tid;
        entry.hash = hash;
        entry.packets.clear();
        for &event in packets {
            let Label::Send { val, .. } = graph.label(event) else {
                unreachable!()
            };
            entry.packets.push((event, *val));
        }
    }
}

pub(crate) fn receive_or_finished(next: &ThreadNext) -> bool {
    match next {
        ThreadNext::Finished => true,
        ThreadNext::Next(Label::Recv {
            pred,
            blocking: true,
            timing: ReceiveTiming::Abstract,
        }) => pred.is_any(),
        _ => false,
    }
}

/// Inputs are the explorer's already consistent graph and exact program views.
/// `None` is unknown, never a proof of failure or an inconclusive search cutoff.
pub(crate) fn certify<'a, P: Program>(
    program: &P,
    graph: &'a ExecutionGraph,
    traces: &[Vec<Option<Val>>],
    nexts: &[ThreadNext],
    labels: &'a [TraceLabel],
    budget: ReceiveTailBudget,
) -> Option<ReceiveTailCertificate<'a>> {
    if !program.annotations_are_local()
        || budget.max_states == 0
        || budget.max_pending_per_thread == 0
        || !nexts.iter().all(receive_or_finished)
    {
        return None;
    }
    let mut pending = vec![Vec::new(); program.num_threads()];
    for send in graph.iter_sends() {
        let Label::Send {
            model: Model::Asyn,
            dst,
            window,
            ..
        } = graph.label(send)
        else {
            return None;
        };
        if !window.is_untimed() {
            return None;
        }
        if !graph.is_read(send) {
            let row = pending.get_mut(*dst)?;
            row.push(send);
            // Bound the recursive proof stack even with an excessive caller budget.
            if row.len() > budget.max_pending_per_thread.min(64) {
                return None;
            }
        }
    }
    for receive in graph.iter_recvs() {
        if !matches!(
            graph.label(receive),
            Label::Recv {
                timing: ReceiveTiming::Abstract,
                ..
            }
        ) {
            return None;
        }
    }
    for tid in 0..graph.num_threads() {
        if (0..graph.thread_len(tid)).any(|idx| graph.label(EventId::new(tid, idx)).is_error()) {
            return None;
        }
    }
    let mut proof = Proof {
        program,
        traces: Vec::new(),
        labels,
        remaining_states: budget.max_states,
    };
    for (tid, row) in pending.iter().enumerate() {
        // All next events have already been validated. With no pending input,
        // Finished or blocking Any is quiescent without another program query.
        if row.is_empty() {
            continue;
        }
        if matches!(nexts[tid], ThreadNext::Finished) {
            return None;
        }
        let identity = graph
            .program_prefix_identity(tid, graph.thread_len(tid))
            .filter(|&(namespace, _)| program.prefix_namespace() == Some(namespace));
        let hash = identity.map(|identity| memo_hash(identity, tid, row));
        if identity.zip(hash).is_some_and(|(identity, hash)| {
            LOCAL_MEMO.with(|cache| cache.borrow().contains(identity, tid, graph, row, hash))
        }) {
            continue;
        }
        if proof.traces.is_empty() {
            proof.traces = traces.to_vec();
        }
        let mut values: Vec<(Val, usize)> = Vec::new();
        for &send in row {
            let Label::Send { val, .. } = graph.label(send) else {
                unreachable!()
            };
            if let Some((_, count)) = values.iter_mut().find(|(value, _)| value == val) {
                *count += 1;
            } else {
                values.push((*val, 1));
            }
        }
        if !proof.visit(tid, &mut values, row.len(), Some(&nexts[tid])) {
            return None;
        }
        if let Some((identity, hash)) = identity.zip(hash) {
            LOCAL_MEMO.with(|cache| cache.borrow_mut().insert(identity, tid, graph, row, hash));
        }
    }
    Some(ReceiveTailCertificate {
        graph,
        labels,
        pending,
        states_checked: budget.max_states - proof.remaining_states,
    })
}

struct Proof<'a, P> {
    program: &'a P,
    traces: Vec<Vec<Option<Val>>>,
    labels: &'a [TraceLabel],
    remaining_states: usize,
}

impl<P: Program> Proof<'_, P> {
    fn visit(
        &mut self,
        tid: usize,
        values: &mut [(Val, usize)],
        remaining: usize,
        root: Option<&ThreadNext>,
    ) -> bool {
        if self.remaining_states == 0 {
            return false;
        }
        self.remaining_states -= 1;
        let next = match root {
            Some(next) => next.clone(),
            None => {
                let next = self.program.next_thread(tid, &self.traces[tid]);
                if self.program.labels(&self.traces) != self.labels {
                    return false;
                }
                next
            }
        };
        if !receive_or_finished(&next) {
            return false;
        }
        if remaining == 0 {
            return true;
        }
        if matches!(next, ThreadNext::Finished) {
            return false;
        }
        for index in 0..values.len() {
            if values[index].1 == 0 {
                continue;
            }
            values[index].1 -= 1;
            self.traces[tid].push(Some(values[index].0));
            let silent = self.visit(tid, values, remaining - 1, None);
            self.traces[tid].pop();
            values[index].1 += 1;
            if !silent {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod memo_tests {
    use super::*;
    use crate::program::replay_cache::CachedProgram;
    use crate::scheduler::traces_of;
    use crate::{Pred, System};

    fn packet_graph(first: &str, second: &str) -> (ExecutionGraph, Vec<EventId>) {
        let mut graph = ExecutionGraph::new();
        let packets = vec![
            graph.add_event(0, Label::send(Model::Asyn, 1, first)),
            graph.add_event(0, Label::send(Model::Asyn, 1, second)),
        ];
        (graph, packets)
    }

    #[test]
    fn local_memo_compares_payloads_multiplicity_epoch_namespace_and_actor() {
        let (graph, packets) = packet_graph("a", "a");
        let identity = (77, 9);
        let hash = memo_hash(identity, 1, &packets);
        let mut memo = LocalMemo::default();
        memo.insert(identity, 1, &graph, &packets, hash);
        assert!(memo.contains(identity, 1, &graph, &packets, hash));

        let (changed, same_ids) = packet_graph("a", "b");
        assert_eq!(packets, same_ids);
        // Hash intentionally need not inspect payload bytes. Exact Val equality
        // is still mandatory even when every send identity and the hash match.
        assert!(!memo.contains(identity, 1, &changed, &same_ids, hash));
        assert!(!memo.contains(identity, 1, &graph, &packets[..1], hash));
        assert!(!memo.contains((77, (1 << 32) | 9), 1, &graph, &packets, hash));
        assert!(!memo.contains((78, 9), 1, &graph, &packets, hash));
        assert!(!memo.contains(identity, 2, &graph, &packets, hash));
    }

    fn system() -> System {
        let mut system = System::new();
        system.add(|ctx| async move {
            ctx.send(1, "a", Model::Asyn);
            ctx.send(1, "b", Model::Asyn);
            ctx.send(2, "peer", Model::Asyn);
        });
        system.add(|ctx| async move {
            loop {
                ctx.recv_any().await;
            }
        });
        system.add(|ctx| async move {
            ctx.recv_any().await;
            ctx.insert_label("peer has received");
        });
        system
    }

    fn program() -> CachedProgram<System> {
        CachedProgram::new(system())
    }

    struct NoMetadataSystem(System);

    impl Program for NoMetadataSystem {
        fn annotations_are_local(&self) -> bool {
            self.0.annotations_are_local()
        }
        fn num_threads(&self) -> usize {
            self.0.num_threads()
        }
        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            self.0.next(traces)
        }
        fn next_thread(&self, tid: usize, trace: &[Option<Val>]) -> ThreadNext {
            self.0.next_thread(tid, trace)
        }
        fn labels(&self, traces: &[Vec<Option<Val>>]) -> Vec<TraceLabel> {
            self.0.labels(traces)
        }
    }

    fn graph(peer_received: bool) -> ExecutionGraph {
        let mut graph = ExecutionGraph::new();
        graph.add_event(0, Label::send(Model::Asyn, 1, "a"));
        graph.add_event(0, Label::send(Model::Asyn, 1, "b"));
        let peer = graph.add_event(0, Label::send(Model::Asyn, 2, "peer"));
        if peer_received {
            let receive = graph.add_event(2, Label::recv(Pred::any()));
            graph.set_rf(receive, Some(peer));
        }
        graph
    }

    fn check<P: Program>(
        program: &P,
        mut graph: ExecutionGraph,
        metadata: bool,
        budget: ReceiveTailBudget,
    ) -> Option<usize> {
        let traces = traces_of(&graph, program.num_threads());
        let nexts = program.next(&traces);
        let labels = program.labels(&traces);
        if metadata {
            graph.reset_program_prefix_namespace(program.prefix_namespace().unwrap());
            for (tid, trace) in traces.iter().enumerate() {
                if let Some(idx) = trace.len().checked_sub(1) {
                    let (_, cursor) = program.next_thread_cursor(tid, trace);
                    let token = program.persist_cursor(tid, cursor.unwrap()).unwrap();
                    graph.set_program_prefix(EventId::new(tid, idx), token);
                }
            }
        }
        certify(program, &graph, &traces, &nexts, &labels, budget)
            .map(|certificate| certificate.states_checked())
    }

    #[test]
    fn positive_local_proof_survives_other_actor_history_and_annotation_changes() {
        let program = program();
        let budget = ReceiveTailBudget::default();
        // Process 1's suffix is silent, but process 2 introduces an annotation.
        // Its failing global query may retain only the successful local proof.
        assert_eq!(check(&program, graph(false), true, budget), None);
        // Process 2 has now received. Process 1's exact prefix and mailbox are
        // unchanged, although the full graph and baseline labels are different.
        assert_eq!(check(&program, graph(true), true, budget), Some(0));
        assert_eq!(check(&program, graph(false), true, budget), None);
    }

    #[test]
    fn missing_metadata_uses_exact_local_proof_even_after_a_memo_hit() {
        let program = program();
        let budget = ReceiveTailBudget::default();
        assert!(check(&program, graph(true), true, budget).unwrap() > 0);
        assert_eq!(check(&program, graph(true), true, budget), Some(0));
        assert!(check(&program, graph(true), false, budget).unwrap() > 0);
        let no_metadata = NoMetadataSystem(system());
        assert_eq!(no_metadata.prefix_namespace(), None);
        assert!(no_metadata.annotations_are_local());
        assert!(check(&no_metadata, graph(true), false, budget).unwrap() > 0);
        assert!(check(&no_metadata, graph(true), false, budget).unwrap() > 0);
    }

    #[test]
    fn budget_exhaustion_is_not_a_positive_cache_entry() {
        let program = program();
        assert_eq!(
            check(
                &program,
                graph(true),
                true,
                ReceiveTailBudget {
                    max_states: 1,
                    max_pending_per_thread: 8
                }
            ),
            None
        );
        assert!(check(&program, graph(true), true, ReceiveTailBudget::default()).unwrap() > 0);
        assert_eq!(
            check(&program, graph(true), true, ReceiveTailBudget::default()),
            Some(0)
        );
    }

    #[derive(Default)]
    struct GlobalAnnotations;

    impl Program for GlobalAnnotations {
        fn num_threads(&self) -> usize {
            3
        }

        fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            (0..3)
                .map(|tid| match (tid, traces[tid].len()) {
                    (0, 0) => ThreadNext::Next(Label::send(Model::Asyn, 1, "a")),
                    (0, 1) => ThreadNext::Next(Label::send(Model::Asyn, 2, "b")),
                    (1 | 2, 0) => ThreadNext::Next(Label::recv(Pred::any())),
                    _ => ThreadNext::Finished,
                })
                .collect()
        }

        fn labels(&self, traces: &[Vec<Option<Val>>]) -> Vec<TraceLabel> {
            if !traces[1].is_empty() && !traces[2].is_empty() {
                vec![TraceLabel {
                    tid: 1,
                    position: 1,
                    value: "both have received".into(),
                }]
            } else {
                Vec::new()
            }
        }
    }

    #[test]
    fn global_annotations_require_normal_enumeration_not_factorized_proofs() {
        use crate::{Config, EventCountingObserver, Execution, ExecutionKind, Observer};
        use std::sync::atomic::{AtomicUsize, Ordering};

        let program = CachedProgram::new(GlobalAnnotations);
        assert!(!program.annotations_are_local());
        let mut prefix = ExecutionGraph::new();
        prefix.add_event(0, Label::send(Model::Asyn, 1, "a"));
        prefix.add_event(0, Label::send(Model::Asyn, 2, "b"));
        let traces = traces_of(&prefix, 3);
        let nexts = program.next(&traces);
        let labels = program.labels(&traces);
        assert!(certify(
            &program,
            &prefix,
            &traces,
            &nexts,
            &labels,
            ReceiveTailBudget::default()
        )
        .is_none());

        struct ObserveGlobal(AtomicUsize);
        impl Observer for ObserveGlobal {
            fn receive_tail_candidate(
                &self,
                _graph: &ExecutionGraph,
                _labels: &[TraceLabel],
            ) -> bool {
                true
            }
            fn accept_receive_tail(&self, _certificate: &ReceiveTailCertificate<'_>) -> bool {
                panic!("global annotations must veto factorization before observer acceptance")
            }
            fn on_execution(&self, execution: &Execution, kind: ExecutionKind) {
                assert_eq!(kind, ExecutionKind::Full);
                assert!(execution
                    .labels()
                    .iter()
                    .any(|label| crate::intern::resolve(label.value) == "both have received"));
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }
        let observers = (
            EventCountingObserver::new(),
            ObserveGlobal(AtomicUsize::new(0)),
        );
        crate::explore(
            || GlobalAnnotations,
            &observers,
            Config::default().with_receive_tail(ReceiveTailBudget::default()),
        );
        assert_eq!(observers.0.receive_tails(), 0);
        assert_eq!(observers.0.full(), 1);
        assert_eq!(observers.1 .0.load(Ordering::Relaxed), 1);
    }
}
