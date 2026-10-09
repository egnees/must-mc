//! History-preserving crash cuts of one completed, failure-free Asyn graph.
//! This is an example monitor, not a change to MUST's execution semantics.
//! po/rf closure uses the prefix-closedness requirement in konspekt §3.6.
use std::cell::{OnceCell, RefCell};
#[cfg(test)]
use std::collections::{BTreeMap, VecDeque};
use std::fmt;
use std::sync::OnceLock;

use super::common::{BROADCAST, DELIVERED, MESSAGES, NODES};

const BOUNDARY: &str = "crash:boundary";

pub(super) struct CutDiagnostic {
    pub faulty: Option<usize>,
    pub property: &'static str,
    pub message: &'static str,
    pub target: usize,
    /// Number of committed graph events at each process (annotations excluded).
    pub positions: [usize; NODES],
    /// Included annotations, retaining their original local insertion order.
    pub labels: Vec<must::TraceLabel>,
}

impl fmt::Display for CutDiagnostic {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            out,
            "{} violated for {:?} at node {}",
            self.property, self.message, self.target
        )?;
        match self.faulty {
            Some(node) => writeln!(out, "Crash cut: faulty node {node}"),
            None => writeln!(out, "Crash cut: no faulty node"),
        }?;
        writeln!(out, "Committed event prefixes: {:?}", self.positions)?;
        for label in &self.labels {
            writeln!(
                out,
                "T{} @{}: {}",
                label.tid,
                label.position,
                must::intern::resolve(label.value)
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Kind {
    Event(must::EventId),
    Annotation(usize),
}

struct Step {
    tid: usize,
    kind: Kind,
}

struct View<'a> {
    graph: &'a must::ExecutionGraph,
    labels: &'a [must::TraceLabel],
    steps: Vec<Step>,
    rows: [Vec<usize>; NODES],
    event_steps: [Vec<usize>; NODES],
    readers: [Vec<Option<must::EventId>>; NODES],
}

impl<'a> View<'a> {
    #[cfg(test)]
    fn new(
        graph: &'a must::ExecutionGraph,
        labels: &'a [must::TraceLabel],
    ) -> Result<Self, String> {
        if !must::consistency::consistent(graph) {
            return Err("crash cuts require a consistent completed graph".into());
        }
        Self::trusted(graph, labels)
    }

    // Used only for executions emitted by MUST: its terminal graphs have
    // already passed consistency. Keep the monitor's model/API guards below.
    #[cfg(test)]
    fn trusted(
        graph: &'a must::ExecutionGraph,
        labels: &'a [must::TraceLabel],
    ) -> Result<Self, String> {
        Self::build(graph, labels, false)
    }

    fn build(
        graph: &'a must::ExecutionGraph,
        labels: &'a [must::TraceLabel],
        selective: bool,
    ) -> Result<Self, String> {
        if graph.num_threads() > NODES + 1 || graph.thread_len(NODES) != 0 {
            return Err("crash cuts support only three processes and an inert sink".into());
        }
        let mut previous = None;
        for label in labels {
            if label.tid >= NODES || label.position > graph.thread_len(label.tid) {
                return Err("crash cuts encountered an invalid annotation position".into());
            }
            let position = (label.tid, label.position);
            if previous.is_some_and(|old| old > position) {
                return Err("crash cuts require annotations in local insertion order".into());
            }
            previous = Some(position);
            if must::intern::resolve(label.value) == "crash" {
                return Err("crash cuts require a failure-free input execution".into());
            }
        }
        let mut readers: [Vec<Option<must::EventId>>; NODES] =
            std::array::from_fn(|tid| vec![None; graph.thread_len(tid)]);
        for tid in 0..NODES {
            for idx in 0..graph.thread_len(tid) {
                let event = must::EventId::new(tid, idx);
                match graph.label(event) {
                    must::Label::Send {
                        model, dst, window, ..
                    } if *model == must::Model::Asyn && *dst <= NODES && window.is_untimed() => {}
                    must::Label::Recv {
                        pred,
                        blocking: true,
                        timing: must::ReceiveTiming::Abstract,
                    } if selective || pred.is_any() => {
                        let source = graph.reads_from(event).ok_or_else(|| {
                            "crash cuts require a source for every receive".to_owned()
                        })?;
                        if source.tid >= NODES
                            || !graph.contains(source)
                            || !matches!(graph.label(source), must::Label::Send { dst, .. } if *dst == tid)
                        {
                            return Err("crash cuts encountered an invalid receive source".into());
                        }
                        if readers[source.tid][source.idx].replace(event).is_some() {
                            return Err("crash cuts encountered a send read more than once".into());
                        }
                    }
                    _ => return Err(
                        "crash cuts support only untimed Asyn sends and blocking abstract receives"
                            .into(),
                    ),
                }
            }
        }
        let mut label_counts = [0; NODES];
        for label in labels {
            label_counts[label.tid] += 1;
        }
        let step_counts: [usize; NODES] =
            std::array::from_fn(|tid| graph.thread_len(tid) + label_counts[tid]);
        let mut view = Self {
            graph,
            labels,
            steps: Vec::with_capacity(step_counts.iter().sum()),
            rows: std::array::from_fn(|tid| Vec::with_capacity(step_counts[tid])),
            event_steps: std::array::from_fn(|tid| Vec::with_capacity(graph.thread_len(tid))),
            readers,
        };
        for tid in 0..NODES {
            let mut annotations = labels
                .iter()
                .enumerate()
                .filter(|(_, label)| label.tid == tid)
                .peekable();
            for position in 0..=graph.thread_len(tid) {
                while annotations
                    .peek()
                    .is_some_and(|(_, label)| label.position == position)
                {
                    let (index, _) = annotations.next().unwrap();
                    view.push(tid, Kind::Annotation(index));
                }
                if position < graph.thread_len(tid) {
                    let event = must::EventId::new(tid, position);
                    let step = view.push(tid, Kind::Event(event));
                    view.event_steps[tid].push(step);
                }
            }
        }
        Ok(view)
    }

    fn event_step(&self, event: must::EventId) -> usize {
        self.event_steps[event.tid][event.idx]
    }

    fn reader(&self, event: must::EventId) -> Option<must::EventId> {
        self.readers[event.tid][event.idx]
    }

    fn events(&self) -> impl Iterator<Item = (must::EventId, usize)> + '_ {
        self.event_steps.iter().enumerate().flat_map(|(tid, row)| {
            row.iter()
                .enumerate()
                .map(move |(idx, &step)| (must::EventId::new(tid, idx), step))
        })
    }

    fn push(&mut self, tid: usize, kind: Kind) -> usize {
        let index = self.steps.len();
        self.steps.push(Step { tid, kind });
        self.rows[tid].push(index);
        index
    }

    fn annotation(&self, index: usize) -> Option<&must::TraceLabel> {
        match self.steps[index].kind {
            Kind::Annotation(label) => Some(&self.labels[label]),
            Kind::Event(_) => None,
        }
    }

    fn progresses(&self, index: usize, faulty: Option<usize>) -> bool {
        let step = &self.steps[index];
        match step.kind {
            Kind::Annotation(label) => {
                faulty != Some(step.tid)
                    || must::intern::resolve(self.labels[label].value) != BOUNDARY
            }
            Kind::Event(event) => faulty != Some(step.tid) && self.graph.label(event).is_send(),
        }
    }
}

#[cfg(test)]
struct Horn {
    edges: Vec<Vec<usize>>,
    mandatory: Vec<usize>,
    forbidden: Vec<bool>,
}

#[cfg(test)]
impl Horn {
    fn new(view: &View<'_>, faulty: Option<usize>) -> Self {
        let mut horn = Self {
            edges: vec![Vec::new(); view.steps.len()],
            mandatory: Vec::new(),
            forbidden: vec![false; view.steps.len()],
        };
        for row in &view.rows {
            if let Some(&first) = row.first() {
                if view.progresses(first, faulty) {
                    horn.mandatory.push(first);
                }
            }
            for pair in row.windows(2) {
                horn.edges[pair[1]].push(pair[0]); // po backwards, including annotations.
                if view.progresses(pair[1], faulty) {
                    horn.edges[pair[0]].push(pair[1]);
                }
            }
        }
        for (event, step) in view.events() {
            match view.graph.label(event) {
                must::Label::Recv { .. } => {
                    horn.edges[step].push(view.event_step(view.graph.reads_from(event).unwrap()));
                }
                must::Label::Send { dst, .. }
                    if *dst < NODES && faulty != Some(event.tid) && faulty != Some(*dst) =>
                {
                    if let Some(recv) = view.reader(event) {
                        horn.edges[step].push(view.event_step(recv));
                    } else {
                        // A live-to-live send cannot remain permanently unread.
                        horn.forbidden[step] = true;
                    }
                }
                _ => {}
            }
        }
        horn
    }

    fn closure(&self, seed: usize, excluded: &[usize]) -> Option<Vec<bool>> {
        let mut included = vec![false; self.edges.len()];
        let mut queue = VecDeque::new();
        queue.extend(self.mandatory.iter().copied());
        queue.push_back(seed);
        while let Some(step) = queue.pop_front() {
            if included[step] {
                continue;
            }
            if self.forbidden[step] || excluded.contains(&step) {
                return None;
            }
            included[step] = true;
            queue.extend(self.edges[step].iter().copied());
        }
        Some(included)
    }
}

pub(super) fn analyze_graph(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
) -> Result<Option<CutDiagnostic>, String> {
    // Only real failure-free terminals: a full local prefix remains blocked
    // when the cut removes sends. Receive-tail certificates use another entry.
    let selective = graph
        .iter_recvs()
        .any(|event| graph.label(event).pred().is_some_and(|pred| !pred.is_any()))
        || graph.iter_sends().any(|event| {
            !graph.is_read(event)
                && matches!(graph.label(event), must::Label::Send { dst, .. } if *dst < NODES)
        });
    if selective {
        let view = View::build(graph, labels, true)?;
        if let Some(failure) = check_creation(graph, labels) {
            return Ok(Some(failure));
        }
        return Ok(SelectiveCuts::new(&view).diagnostic());
    }
    analyze_prefix_mode(graph, labels, true, true)
}

struct SelectivePacket {
    bound: usize,
    reader: usize,
    value: must::Val,
}

struct SelectiveCuts<'a, 'g> {
    view: &'a View<'g>,
    bounds: Vec<usize>,
    required: [Vec<[usize; NODES]>; NODES],
    advance: [[Vec<usize>; NODES]; 2],
    incoming: [[Vec<SelectivePacket>; NODES]; NODES],
    enabled: [Vec<OnceCell<[usize; NODES]>>; NODES],
}

impl<'a, 'g> SelectiveCuts<'a, 'g> {
    fn new(view: &'a View<'g>) -> Self {
        let mut bounds = vec![0; view.steps.len()];
        for row in &view.rows {
            for (position, &step) in row.iter().enumerate() {
                bounds[step] = position + 1;
            }
        }
        let required = std::array::from_fn(|tid| {
            let mut row = vec![[0; NODES]; view.rows[tid].len() + 1];
            for (position, &step) in view.rows[tid].iter().enumerate() {
                let mut requirements = row[position];
                if let Kind::Event(event) = view.steps[step].kind {
                    if let Some(source) = view.graph.reads_from(event) {
                        requirements[source.tid] =
                            requirements[source.tid].max(bounds[view.event_step(source)]);
                    }
                }
                row[position + 1] = requirements;
            }
            row
        });
        let advance = std::array::from_fn(|failed| {
            std::array::from_fn(|tid| {
                let mut row: Vec<_> = (0..=view.rows[tid].len()).collect();
                for position in (0..view.rows[tid].len()).rev() {
                    if view.progresses(view.rows[tid][position], (failed != 0).then_some(tid)) {
                        row[position] = row[position + 1];
                    }
                }
                row
            })
        });
        let mut incoming: [[Vec<SelectivePacket>; NODES]; NODES] =
            std::array::from_fn(|_| std::array::from_fn(|_| Vec::new()));
        for (send, step) in view.events() {
            if let must::Label::Send { dst, val, .. } = view.graph.label(send) {
                if *dst < NODES {
                    incoming[*dst][send.tid].push(SelectivePacket {
                        bound: bounds[step],
                        reader: view
                            .reader(send)
                            .map_or(usize::MAX, |read| bounds[view.event_step(read)]),
                        value: *val,
                    });
                }
            }
        }
        let enabled =
            std::array::from_fn(|tid| (0..view.rows[tid].len()).map(|_| OnceCell::new()).collect());
        Self {
            view,
            bounds,
            required,
            advance,
            incoming,
            enabled,
        }
    }

    fn enabling_sources(&self, tid: usize, boundary: usize) -> &[usize; NODES] {
        self.enabled[tid][boundary].get_or_init(|| {
            let step = self.view.rows[tid][boundary];
            let Kind::Event(receive) = self.view.steps[step].kind else {
                return [usize::MAX; NODES];
            };
            let Some(pred) = self.view.graph.label(receive).pred() else {
                return [usize::MAX; NODES];
            };
            std::array::from_fn(|source| {
                self.incoming[tid][source]
                    .iter()
                    .find(|packet| packet.reader > boundary && pred.test_sym(packet.value))
                    .map_or(usize::MAX, |packet| packet.bound)
            })
        })
    }

    fn closure(&self, faulty: Option<usize>, seed: usize) -> [usize; NODES] {
        let mut cuts = [0; NODES];
        cuts[self.view.steps[seed].tid] = self.bounds[seed];
        loop {
            let before = cuts;
            for tid in 0..NODES {
                cuts[tid] = self.advance[usize::from(faulty == Some(tid))][tid][cuts[tid]];
                for (source, required) in self.required[tid][cuts[tid]].iter().enumerate() {
                    cuts[source] = cuts[source].max(*required);
                }
                if faulty != Some(tid) && cuts[tid] < self.view.rows[tid].len() {
                    let enabled = self.enabling_sources(tid, cuts[tid]);
                    if (0..NODES)
                        .any(|source| faulty != Some(source) && cuts[source] >= enabled[source])
                    {
                        // Every extension must leave this enabled boundary;
                        // predicates at later boundaries may differ arbitrarily.
                        cuts[tid] += 1;
                    }
                }
            }
            if cuts == before {
                return cuts;
            }
        }
    }

    fn diagnostic(&self) -> Option<CutDiagnostic> {
        let view = self.view;
        let symbols = annotation_symbols();
        for faulty in std::iter::once(None).chain((0..NODES).map(Some)) {
            for (seed, step) in view.steps.iter().enumerate() {
                let Kind::Annotation(index) = step.kind else {
                    continue;
                };
                let (message, broadcast) = match classify_role(view.labels[index].value, symbols) {
                    Role::Broadcast(message) if faulty != Some(step.tid) => (message, true),
                    Role::Delivery(message) => (message, false),
                    _ => continue,
                };
                let cuts = self.closure(faulty, seed);
                for target in 0..NODES {
                    if faulty == Some(target) || (broadcast && target != step.tid) {
                        continue;
                    }
                    let delivered = view.rows[target][..cuts[target]].iter().any(|&index| {
                        view.annotation(index)
                            .is_some_and(|label| label.value == symbols.deliveries[message])
                    });
                    if !delivered {
                        let mut positions = [0; NODES];
                        let mut labels = Vec::new();
                        for tid in 0..NODES {
                            for &index in &view.rows[tid][..cuts[tid]] {
                                match view.steps[index].kind {
                                    Kind::Event(_) => positions[tid] += 1,
                                    Kind::Annotation(index) => {
                                        labels.push(view.labels[index].clone())
                                    }
                                }
                            }
                        }
                        return Some(CutDiagnostic {
                            faulty,
                            property: if broadcast {
                                "validity"
                            } else {
                                "uniform agreement"
                            },
                            message: MESSAGES[message],
                            target,
                            positions,
                            labels,
                        });
                    }
                }
            }
        }
        None
    }
}

// Called only after the runtime certifies every permutation of these pending
// deliveries drains without sends/errors/nondeterminism/new annotations.
pub(super) fn prove_completed_receive_tail(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
    pending_sends: &[Vec<must::EventId>],
) -> bool {
    PREFIX_WORKSPACE.with(|workspace| {
        prove_tail_cached(
            &mut workspace.borrow_mut(),
            graph,
            labels,
            pending_sends,
            true,
        )
        .unwrap_or(false)
    })
}

pub(super) fn check_creation(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
) -> Option<CutDiagnostic> {
    let symbols = annotation_symbols();
    for (delivery, label) in labels.iter().enumerate() {
        let Some(message) = symbols
            .deliveries
            .iter()
            .position(|&value| value == label.value)
        else {
            continue;
        };
        let broadcast = labels
            .iter()
            .position(|label| label.value == symbols.broadcasts[message]);
        let follows = broadcast.is_some_and(|broadcast| {
            let source = &labels[broadcast];
            if source.tid == label.tid {
                return broadcast < delivery; // Includes same-position annotations.
            }
            let Some(previous) = label.position.checked_sub(1) else {
                return false;
            };
            let next = must::EventId::new(source.tid, source.position);
            let previous = must::EventId::new(label.tid, previous);
            graph.contains(next) && graph.contains(previous) && graph.porf_reaches(next, previous)
        });
        if !follows {
            return Some(CutDiagnostic {
                faulty: None,
                property: "no creation",
                message: MESSAGES[message],
                target: label.tid,
                positions: std::array::from_fn(|tid| graph.thread_len(tid)),
                labels: labels.to_vec(),
            });
        }
    }
    None
}

#[cfg(test)]
fn analyze_parts(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
) -> Result<Option<CutDiagnostic>, String> {
    if !must::consistency::consistent(graph) {
        return Err("crash cuts require a consistent completed graph".into());
    }
    analyze_prefix(graph, labels)
}

#[cfg(test)]
fn analyze_view(view: &View<'_>) -> Option<CutDiagnostic> {
    let index = AnnotationIndex::new(view);
    if index.seeds.len() > 16 {
        // Duplicate annotations can exceed the normal two-input/eight-seed
        // bound. Preserve the exact general behavior rather than truncate.
        return analyze_slow_view(view);
    }
    analyze_parallel(view, &index)
}

#[derive(Clone, Copy)]
enum Role {
    Other,
    Boundary,
    Broadcast(usize),
    Delivery(usize),
}

struct AnnotationSymbols {
    broadcasts: [must::Val; MESSAGES.len()],
    deliveries: [must::Val; MESSAGES.len()],
    boundary: must::Val,
    crash: must::Val,
}

fn annotation_symbols() -> &'static AnnotationSymbols {
    static SYMBOLS: OnceLock<AnnotationSymbols> = OnceLock::new();
    SYMBOLS.get_or_init(|| AnnotationSymbols {
        broadcasts: BROADCAST.map(must::intern::intern),
        deliveries: DELIVERED.map(must::intern::intern),
        boundary: must::intern::intern(BOUNDARY),
        crash: must::intern::intern("crash"),
    })
}

fn classify_role(value: must::Val, symbols: &AnnotationSymbols) -> Role {
    if value == symbols.boundary {
        Role::Boundary
    } else if let Some(message) = symbols.broadcasts.iter().position(|&name| name == value) {
        Role::Broadcast(message)
    } else if let Some(message) = symbols.deliveries.iter().position(|&name| name == value) {
        Role::Delivery(message)
    } else {
        Role::Other
    }
}

#[derive(Clone, Copy)]
enum KeyOp {
    Send(usize),
    Receive(must::EventId),
}

#[derive(Clone, Copy, Default)]
struct PrefixEntry {
    advance: usize,
    required: [usize; NODES],
    forbidden: bool,
}

struct PrefixSeed {
    tid: usize,
    bound: usize,
    message: usize,
    broadcast: bool,
}

#[derive(Default)]
struct PrefixWorkspace {
    rows: [Vec<Kind>; NODES],
    event_bounds: [Vec<usize>; NODES],
    readers: [Vec<Option<must::EventId>>; NODES],
    roles: Vec<Role>,
    label_bounds: Vec<usize>,
    seeds: Vec<PrefixSeed>,
    ordered_seeds: [Vec<usize>; NODES],
    closures: Vec<Option<[usize; NODES]>>,
    delivery_bounds: [[usize; NODES]; MESSAGES.len()],
    tables: [[Vec<PrefixEntry>; NODES]; NODES + 1],
    key: Vec<u64>,
    pass_cache: PassCache,
    key_ops: [Vec<KeyOp>; NODES],
}

const PASS_CACHE_SLOTS: usize = 256;

#[derive(Default)]
struct PassEntry {
    hash: u64,
    key: Vec<u64>,
    valid: bool,
}

struct PassCache {
    entries: [PassEntry; PASS_CACHE_SLOTS],
    #[cfg(test)]
    hits: u64,
    #[cfg(test)]
    certificates: u64,
    #[cfg(test)]
    fallbacks: u64,
}

impl Default for PassCache {
    fn default() -> Self {
        Self {
            entries: std::array::from_fn(|_| PassEntry::default()),
            #[cfg(test)]
            hits: 0,
            #[cfg(test)]
            certificates: 0,
            #[cfg(test)]
            fallbacks: 0,
        }
    }
}

impl PassCache {
    fn contains(&self, key: &[u64], hash: u64) -> bool {
        let entry = &self.entries[hash as usize % PASS_CACHE_SLOTS];
        entry.valid && entry.hash == hash && entry.key == key
    }

    fn insert(&mut self, key: &[u64], hash: u64) {
        let entry = &mut self.entries[hash as usize % PASS_CACHE_SLOTS];
        entry.key.clear();
        entry.key.extend_from_slice(key);
        entry.hash = hash;
        entry.valid = true;
    }
}

fn annotation_layout(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
) -> Result<([usize; NODES], [usize; NODES]), String> {
    if graph.num_threads() > NODES + 1 || graph.thread_len(NODES) != 0 {
        return Err("crash cuts support only three processes and an inert sink".into());
    }
    let mut caps = [0; NODES];
    let mut counts = [0; NODES];
    let mut previous = None;
    let crash = annotation_symbols().crash;
    for label in labels {
        if label.tid >= NODES || label.position > graph.thread_len(label.tid) {
            return Err("crash cuts encountered an invalid annotation position".into());
        }
        let position = (label.tid, label.position);
        if previous.is_some_and(|old| old > position) {
            return Err("crash cuts require annotations in local insertion order".into());
        }
        if label.value == crash {
            return Err("crash cuts require a failure-free input execution".into());
        }
        previous = Some(position);
        caps[label.tid] = caps[label.tid].max(label.position);
        counts[label.tid] += 1;
    }
    Ok((caps, counts))
}

fn reader_key(reader: Option<must::EventId>, caps: &[usize; NODES]) -> (u64, u64) {
    match reader {
        None => (3, 0),
        Some(reader) if reader.idx < caps[reader.tid] => (4, (reader.idx + 1) as u64),
        Some(reader) => (5, caps[reader.tid] as u64),
    }
}

fn key_hash(key: &[u64]) -> u64 {
    key.iter().fold(0xcbf29ce484222325, |hash, &word| {
        (hash ^ word).wrapping_mul(0x100000001b3)
    })
}

fn role_code(role: Role) -> u64 {
    match role {
        Role::Other => 0,
        Role::Boundary => 1,
        Role::Broadcast(message) => 2 + message as u64,
        Role::Delivery(message) => 4 + message as u64,
    }
}

fn append_packed(key: &mut Vec<u64>, class: u64, bound: u64) {
    // Tags 0..2 are rf source threads; 3..5 are reader None/Exact/Tail.
    // The escape tag 7 can never occur in a compact word.
    if bound <= u64::MAX >> 3 {
        key.push((bound << 3) | class);
    } else {
        key.extend_from_slice(&[u64::MAX, class, bound]);
    }
}

thread_local! {
    // The monitor invokes no process callbacks and is not reentrant. Each
    // explorer worker reuses its own buffers; larger histories grow naturally.
    static PREFIX_WORKSPACE: RefCell<PrefixWorkspace> = RefCell::new(PrefixWorkspace::default());
}

impl PrefixWorkspace {
    fn prepare_key(
        &mut self,
        graph: &must::ExecutionGraph,
        labels: &[must::TraceLabel],
        certified: bool,
        pending: Option<&[Vec<must::EventId>]>,
    ) -> Result<[usize; NODES], String> {
        let (mut caps, label_counts) = annotation_layout(graph, labels)?;
        let symbols = annotation_symbols();
        for tid in 0..NODES {
            self.readers[tid].resize(graph.thread_len(tid), None);
            self.readers[tid].fill(None);
            self.key_ops[tid].clear();
            self.key_ops[tid].reserve(graph.thread_len(tid));
        }
        for (tid, cap) in caps.iter_mut().enumerate() {
            for idx in 0..graph.thread_len(tid) {
                let event = must::EventId::new(tid, idx);
                match graph.label(event) {
                    must::Label::Send {
                        model, dst, window, ..
                    } if *model == must::Model::Asyn && *dst <= NODES && window.is_untimed() => {
                        *cap = (*cap).max(idx + 1);
                        self.key_ops[tid].push(KeyOp::Send(*dst));
                    }
                    must::Label::Recv {
                        pred,
                        blocking: true,
                        timing: must::ReceiveTiming::Abstract,
                    } if pred.is_any() => {
                        let source = graph.reads_from(event).ok_or_else(|| {
                            "crash cuts require a source for every receive".to_owned()
                        })?;
                        if !certified
                            && (source.tid >= NODES
                                || !graph.contains(source)
                                || !matches!(graph.label(source), must::Label::Send { dst, .. } if *dst == tid))
                        {
                            return Err("crash cuts encountered an invalid receive source".into());
                        }
                        let previous = self.readers[source.tid][source.idx].replace(event);
                        if !certified && previous.is_some() {
                            return Err("crash cuts encountered a send read more than once".into());
                        }
                        self.key_ops[tid].push(KeyOp::Receive(source));
                    }
                    _ => {
                        return Err(
                            "crash cuts support only untimed Asyn sends and blocking recv_any"
                                .into(),
                        )
                    }
                }
            }
        }
        if let Some(pending) = pending {
            self.bind_pending(graph, pending)?;
        }
        self.key.clear();
        let identities: [Option<(u64, u64)>; NODES] =
            std::array::from_fn(|tid| graph.program_prefix_identity(tid, caps[tid]));
        if let (
            true,
            [Some((namespace, zero)), Some((one_namespace, one)), Some((two_namespace, two))],
        ) = (certified, identities)
        {
            if namespace == one_namespace && namespace == two_namespace {
                // Exact local-history identities determine all retained local
                // opcodes, destinations and annotations. Actual rf identities
                // and send reader classes remain separate graph information.
                self.key.extend_from_slice(&[
                    1,
                    namespace,
                    caps[0] as u64,
                    zero,
                    caps[1] as u64,
                    one,
                    caps[2] as u64,
                    two,
                ]);
                for tid in 0..NODES {
                    for (idx, &op) in self.key_ops[tid][..caps[tid]].iter().enumerate() {
                        match op {
                            KeyOp::Send(_) => {
                                let (class, bound) = reader_key(self.readers[tid][idx], &caps);
                                append_packed(&mut self.key, class, bound);
                            }
                            KeyOp::Receive(source) => {
                                append_packed(&mut self.key, source.tid as u64, source.idx as u64)
                            }
                        }
                    }
                }
                return Ok(caps);
            }
        }
        self.key.push(0); // Structural/mixed-metadata format, never aliases compact.
        for tid in 0..NODES {
            let identity = identities[tid];
            let (present, namespace, token) =
                identity.map_or((0, 0, 0), |(namespace, token)| (1, namespace, token));
            self.key.extend_from_slice(&[
                caps[tid] as u64,
                present,
                namespace,
                token,
                label_counts[tid] as u64,
            ]);
            for idx in 0..caps[tid] {
                match self.key_ops[tid][idx] {
                    KeyOp::Send(dst) => {
                        if identity.is_none() {
                            self.key.push((dst + 1) as u64);
                        }
                        let (class, bound) = reader_key(self.readers[tid][idx], &caps);
                        self.key.extend_from_slice(&[class, bound]);
                    }
                    KeyOp::Receive(source) => {
                        if identity.is_none() {
                            self.key.push(0);
                        }
                        self.key
                            .extend_from_slice(&[source.tid as u64, source.idx as u64]);
                    }
                }
            }
            for label in labels.iter().filter(|label| label.tid == tid) {
                self.key.extend_from_slice(&[
                    label.position as u64,
                    role_code(classify_role(label.value, symbols)),
                ]);
            }
        }
        Ok(caps)
    }

    fn bind_pending(
        &mut self,
        graph: &must::ExecutionGraph,
        pending: &[Vec<must::EventId>],
    ) -> Result<(), String> {
        if !(NODES..=NODES + 1).contains(&pending.len()) {
            return Err("receive tail requires pending lists for three processes".into());
        }
        for (destination, sends) in pending.iter().enumerate() {
            for &send in sends {
                if send.tid >= NODES
                    || !graph.contains(send)
                    || !matches!(graph.label(send), must::Label::Send { dst, .. } if *dst == destination)
                    || self.readers[send.tid][send.idx].is_some()
                {
                    return Err(
                        "receive tail pending list is not an exact unread-send binding".into(),
                    );
                }
                if destination < NODES {
                    // This reader is outside the current graph. Its only
                    // projected implication is the receiver's retained cap.
                    self.readers[send.tid][send.idx] = Some(must::EventId::new(
                        destination,
                        graph.thread_len(destination),
                    ));
                }
            }
        }
        for tid in 0..NODES {
            for idx in 0..graph.thread_len(tid) {
                let event = must::EventId::new(tid, idx);
                if matches!(graph.label(event), must::Label::Send { dst, .. } if *dst < NODES)
                    && self.readers[tid][idx].is_none()
                {
                    return Err("receive tail pending list omitted an unread send".into());
                }
            }
        }
        Ok(())
    }

    fn prepare(
        &mut self,
        graph: &must::ExecutionGraph,
        labels: &[must::TraceLabel],
    ) -> Result<(), String> {
        let (_, label_counts) = annotation_layout(graph, labels)?;
        let symbols = annotation_symbols();
        self.roles.clear();
        self.roles.extend(
            labels
                .iter()
                .map(|label| classify_role(label.value, symbols)),
        );
        self.seeds.clear();
        self.label_bounds.resize(labels.len(), 0);
        self.delivery_bounds = [[usize::MAX; NODES]; MESSAGES.len()];
        for (tid, &label_count) in label_counts.iter().enumerate() {
            self.rows[tid].clear();
            self.rows[tid].reserve(graph.thread_len(tid) + label_count);
            self.event_bounds[tid].clear();
            self.event_bounds[tid].reserve(graph.thread_len(tid));
            self.readers[tid].resize(graph.thread_len(tid), None);
            self.readers[tid].fill(None);
            let mut annotations = labels
                .iter()
                .enumerate()
                .filter(|(_, label)| label.tid == tid)
                .peekable();
            for position in 0..=graph.thread_len(tid) {
                while annotations
                    .peek()
                    .is_some_and(|(_, label)| label.position == position)
                {
                    let (index, _) = annotations.next().unwrap();
                    self.rows[tid].push(Kind::Annotation(index));
                    let bound = self.rows[tid].len();
                    self.label_bounds[index] = bound;
                    if let Role::Delivery(message) = self.roles[index] {
                        self.delivery_bounds[message][tid] =
                            self.delivery_bounds[message][tid].min(bound);
                    }
                }
                if position < graph.thread_len(tid) {
                    self.rows[tid].push(Kind::Event(must::EventId::new(tid, position)));
                    self.event_bounds[tid].push(self.rows[tid].len());
                }
            }
        }
        // Terminal graphs are already consistency-certified by MUST. Retain
        // all API/model/source guards without repeating its full validator.
        for tid in 0..NODES {
            for idx in 0..graph.thread_len(tid) {
                let event = must::EventId::new(tid, idx);
                match graph.label(event) {
                    must::Label::Send {
                        model, dst, window, ..
                    } if *model == must::Model::Asyn && *dst <= NODES && window.is_untimed() => {}
                    must::Label::Recv {
                        pred,
                        blocking: true,
                        timing: must::ReceiveTiming::Abstract,
                    } if pred.is_any() => {
                        let source = graph.reads_from(event).ok_or_else(|| {
                            "crash cuts require a source for every receive".to_owned()
                        })?;
                        if source.tid >= NODES
                            || !graph.contains(source)
                            || !matches!(graph.label(source), must::Label::Send { dst, .. } if *dst == tid)
                        {
                            return Err("crash cuts encountered an invalid receive source".into());
                        }
                        if self.readers[source.tid][source.idx]
                            .replace(event)
                            .is_some()
                        {
                            return Err("crash cuts encountered a send read more than once".into());
                        }
                    }
                    _ => {
                        return Err(
                            "crash cuts support only untimed Asyn sends and blocking recv_any"
                                .into(),
                        )
                    }
                }
            }
        }
        for message in 0..MESSAGES.len() {
            for (index, role) in self.roles.iter().enumerate() {
                let broadcast = match *role {
                    Role::Broadcast(found) if found == message => true,
                    Role::Delivery(found) if found == message => false,
                    _ => continue,
                };
                self.seeds.push(PrefixSeed {
                    tid: labels[index].tid,
                    bound: self.label_bounds[index],
                    message,
                    broadcast,
                });
            }
        }
        for tid in 0..NODES {
            self.ordered_seeds[tid].clear();
            for (index, seed) in self.seeds.iter().enumerate() {
                if seed.tid == tid {
                    self.ordered_seeds[tid].push(index);
                }
            }
            self.ordered_seeds[tid].sort_unstable_by_key(|&index| self.seeds[index].bound);
        }
        self.closures.resize(self.seeds.len(), None);
        Ok(())
    }

    fn retain_prefixes(&mut self, caps: &[usize; NODES]) {
        for (row, &cap) in self.rows.iter_mut().zip(caps) {
            let retained = row
                .iter()
                .position(|kind| matches!(kind, Kind::Event(event) if event.idx >= cap))
                .unwrap_or(row.len());
            row.truncate(retained);
        }
    }

    fn build_tables(&mut self, graph: &must::ExecutionGraph, projected: Option<[usize; NODES]>) {
        for slot in 0..=NODES {
            let faulty = slot.checked_sub(1);
            for tid in 0..NODES {
                let row = &self.rows[tid];
                let table = &mut self.tables[slot][tid];
                table.resize(row.len() + 1, PrefixEntry::default());
                table[0] = PrefixEntry::default();
                for (position, &kind) in row.iter().enumerate() {
                    let mut entry = table[position];
                    entry.advance = 0;
                    if let Kind::Event(event) = kind {
                        let required = match graph.label(event) {
                            must::Label::Recv { .. } => graph.reads_from(event),
                            must::Label::Send { dst, .. }
                                if *dst < NODES && faulty != Some(tid) && faulty != Some(*dst) =>
                            {
                                let reader = self.readers[tid][event.idx];
                                entry.forbidden |= reader.is_none();
                                reader
                            }
                            _ => None,
                        };
                        if let Some(event) = required {
                            let bound =
                                if projected.is_some_and(|caps| event.idx >= caps[event.tid]) {
                                    // A tail reader entails its entire retained po
                                    // prefix. Drop only the additional tail facts.
                                    self.rows[event.tid].len()
                                } else {
                                    self.event_bounds[event.tid][event.idx]
                                };
                            entry.required[event.tid] = entry.required[event.tid].max(bound);
                        }
                    }
                    table[position + 1] = entry;
                }
                // At prefix p, immediately execute the mandatory local segment
                // until the next recv or permitted crash boundary.
                let mut stop = row.len();
                table[row.len()].advance = stop;
                for position in (0..row.len()).rev() {
                    let progresses = match row[position] {
                        Kind::Annotation(index) => {
                            faulty != Some(tid) || !matches!(self.roles[index], Role::Boundary)
                        }
                        Kind::Event(event) => faulty != Some(tid) && graph.label(event).is_send(),
                    };
                    if !progresses {
                        stop = position;
                    }
                    table[position].advance = stop;
                }
            }
        }
    }

    fn close(&self, slot: usize, mut cuts: [usize; NODES]) -> Option<[usize; NODES]> {
        loop {
            let mut changed = false;
            for tid in 0..NODES {
                let table = &self.tables[slot][tid];
                let next = table[cuts[tid]].advance;
                if next != cuts[tid] {
                    cuts[tid] = next;
                    changed = true;
                }
                let entry = table[next];
                if entry.forbidden {
                    return None;
                }
                for (destination, &required) in entry.required.iter().enumerate() {
                    if required > cuts[destination] {
                        cuts[destination] = required;
                        changed = true;
                    }
                }
            }
            if !changed {
                return Some(cuts);
            }
        }
    }

    fn diagnostic(&mut self, labels: &[must::TraceLabel]) -> Option<CutDiagnostic> {
        for slot in 0..=NODES {
            let faulty = slot.checked_sub(1);
            let Some(base) = self.close(slot, [0; NODES]) else {
                continue;
            };
            let covered: [bool; MESSAGES.len()] = std::array::from_fn(|message| {
                (0..NODES).all(|tid| {
                    faulty == Some(tid) || base[tid] >= self.delivery_bounds[message][tid]
                })
            });
            if covered.iter().all(|&complete| complete) {
                continue;
            }
            self.closures.fill(None);
            for tid in 0..NODES {
                // Increasing seeds on one process form nested least closures.
                // Different origins restart from base and are never combined.
                let mut current = base;
                for &index in &self.ordered_seeds[tid] {
                    let seed = &self.seeds[index];
                    if covered[seed.message]
                        || (seed.broadcast && faulty == Some(seed.tid))
                        || (seed.broadcast
                            && base[seed.tid] >= self.delivery_bounds[seed.message][seed.tid])
                    {
                        continue;
                    }
                    if seed.bound > current[tid] {
                        current[tid] = seed.bound;
                        let Some(next) = self.close(slot, current) else {
                            break;
                        };
                        current = next;
                    }
                    self.closures[index] = Some(current);
                }
            }
            for (index, seed) in self.seeds.iter().enumerate() {
                if covered[seed.message] || (seed.broadcast && faulty == Some(seed.tid)) {
                    continue;
                }
                if seed.broadcast && base[seed.tid] >= self.delivery_bounds[seed.message][seed.tid]
                {
                    continue;
                }
                let Some(cuts) = self.closures[index] else {
                    continue;
                };
                for target in 0..NODES {
                    if (seed.broadcast && target != seed.tid)
                        || (!seed.broadcast && faulty == Some(target))
                        || cuts[target] >= self.delivery_bounds[seed.message][target]
                    {
                        continue;
                    }
                    let mut positions = [0; NODES];
                    let mut kept_labels = Vec::new();
                    for tid in 0..NODES {
                        for kind in &self.rows[tid][..cuts[tid]] {
                            match *kind {
                                Kind::Event(_) => positions[tid] += 1,
                                Kind::Annotation(index) => kept_labels.push(labels[index].clone()),
                            }
                        }
                    }
                    return Some(CutDiagnostic {
                        faulty,
                        property: if seed.broadcast {
                            "validity"
                        } else {
                            "uniform agreement"
                        },
                        message: MESSAGES[seed.message],
                        target,
                        positions,
                        labels: kept_labels,
                    });
                }
            }
        }
        None
    }
}

#[cfg(test)]
fn analyze_prefix(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
) -> Result<Option<CutDiagnostic>, String> {
    analyze_prefix_mode(graph, labels, false, false)
}

fn analyze_prefix_mode(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
    certified: bool,
    combined: bool,
) -> Result<Option<CutDiagnostic>, String> {
    PREFIX_WORKSPACE.with(|workspace| {
        let mut workspace = workspace.borrow_mut();
        analyze_cached_mode(&mut workspace, graph, labels, certified, combined)
    })
}

#[cfg(test)]
fn analyze_cached(
    workspace: &mut PrefixWorkspace,
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
) -> Result<Option<CutDiagnostic>, String> {
    analyze_cached_mode(workspace, graph, labels, false, false)
}

fn analyze_cached_mode(
    workspace: &mut PrefixWorkspace,
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
    certified: bool,
    combined: bool,
) -> Result<Option<CutDiagnostic>, String> {
    let caps = workspace.prepare_key(graph, labels, certified, None)?;
    workspace.key.push(u64::from(combined));
    let hash = key_hash(&workspace.key);
    if workspace.pass_cache.contains(&workspace.key, hash) {
        #[cfg(test)]
        {
            workspace.pass_cache.hits += 1;
        }
        return Ok(None);
    }
    if combined {
        // Every send and annotation is retained in the projection. A deleted
        // receive-only tail has no outgoing path back to a delivery label, so
        // No Creation depends only on the exact retained-prefix cache key.
        if let Some(failure) = check_creation(graph, labels) {
            return Ok(Some(failure));
        }
    }
    workspace.prepare(graph, labels)?;
    workspace.retain_prefixes(&caps);
    workspace.build_tables(graph, Some(caps));
    if workspace.diagnostic(labels).is_none() {
        // Projected rules under-approximate every full graph with this
        // exact key. Only PASS is transferable; never cache a failure.
        workspace.pass_cache.insert(&workspace.key, hash);
        #[cfg(test)]
        {
            workspace.pass_cache.certificates += 1;
        }
        return Ok(None);
    }
    #[cfg(test)]
    {
        workspace.pass_cache.fallbacks += 1;
    }
    workspace.prepare(graph, labels)?;
    workspace.build_tables(graph, None);
    Ok(workspace.diagnostic(labels))
}

fn prove_tail_cached(
    workspace: &mut PrefixWorkspace,
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
    pending: &[Vec<must::EventId>],
    combined: bool,
) -> Result<bool, String> {
    let caps = workspace.prepare_key(graph, labels, true, Some(pending))?;
    workspace.key.push(2 | u64::from(combined));
    let hash = key_hash(&workspace.key);
    if workspace.pass_cache.contains(&workspace.key, hash) {
        #[cfg(test)]
        {
            workspace.pass_cache.hits += 1;
        }
        return Ok(true);
    }
    if combined && check_creation(graph, labels).is_some() {
        return Ok(false);
    }
    workspace.prepare(graph, labels)?;
    workspace.bind_pending(graph, pending)?;
    workspace.retain_prefixes(&caps);
    workspace.build_tables(graph, Some(caps));
    if workspace.diagnostic(labels).is_none() {
        workspace.pass_cache.insert(&workspace.key, hash);
        #[cfg(test)]
        {
            workspace.pass_cache.certificates += 1;
        }
        Ok(true)
    } else {
        // This prefix is not a full execution. Unknown must resume ordinary
        // exploration; a full solver with missing future rf would be unsound.
        #[cfg(test)]
        {
            workspace.pass_cache.fallbacks += 1;
        }
        Ok(false)
    }
}

#[cfg(test)]
struct Seed {
    step: usize,
    message: usize,
    broadcast: bool,
    tid: usize,
}

#[cfg(test)]
struct AnnotationIndex {
    roles: Vec<Role>,
    seeds: Vec<Seed>,
    deliveries: [[Vec<usize>; NODES]; MESSAGES.len()],
}

#[cfg(test)]
impl AnnotationIndex {
    fn new(view: &View<'_>) -> Self {
        let mut roles = vec![Role::Other; view.steps.len()];
        let mut deliveries: [[Vec<usize>; NODES]; MESSAGES.len()] =
            std::array::from_fn(|_| std::array::from_fn(|_| Vec::new()));
        for (step, role) in roles.iter_mut().enumerate() {
            let Some(label) = view.annotation(step) else {
                continue;
            };
            let value = must::intern::resolve(label.value);
            if value == BOUNDARY {
                *role = Role::Boundary;
            } else if let Some(message) = BROADCAST.iter().position(|&name| value == name) {
                *role = Role::Broadcast(message);
            } else if let Some(message) = DELIVERED.iter().position(|&name| value == name) {
                *role = Role::Delivery(message);
                deliveries[message][label.tid].push(step);
            }
        }
        let mut seeds = Vec::new();
        // Preserve the slow monitor's message/step order, including duplicates.
        for message in 0..MESSAGES.len() {
            for (step, role) in roles.iter().enumerate() {
                let broadcast = match *role {
                    Role::Broadcast(found) if found == message => true,
                    Role::Delivery(found) if found == message => false,
                    _ => continue,
                };
                seeds.push(Seed {
                    step,
                    message,
                    broadcast,
                    tid: view.steps[step].tid,
                });
            }
        }
        Self {
            roles,
            seeds,
            deliveries,
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Default)]
struct Edge {
    target: usize,
    lanes: u64,
}

#[cfg(test)]
#[derive(Clone, Default)]
struct Edges {
    entries: [Edge; 3],
    len: usize,
}

#[cfg(test)]
impl Edges {
    fn add(&mut self, target: usize, lanes: u64) {
        if lanes == 0 {
            return;
        }
        for edge in &mut self.entries[..self.len] {
            if edge.target == target {
                edge.lanes |= lanes;
                return;
            }
        }
        // Each step has at most po-backward, progress-forward, and rf/transport.
        assert!(self.len < self.entries.len());
        self.entries[self.len] = Edge { target, lanes };
        self.len += 1;
    }
}

#[cfg(test)]
fn add_lanes(
    step: usize,
    lanes: u64,
    masks: &mut [u64],
    queued: &mut [bool],
    queue: &mut VecDeque<usize>,
) {
    let added = lanes & !masks[step];
    if added != 0 {
        masks[step] |= added;
        if !queued[step] {
            queued[step] = true;
            queue.push_back(step);
        }
    }
}

#[cfg(test)]
fn analyze_parallel(view: &View<'_>, index: &AnnotationIndex) -> Option<CutDiagnostic> {
    let count = index.seeds.len();
    if count == 0 {
        return None;
    }
    let fault_slots = [None, Some(0), Some(1), Some(2)];
    let mut active = 0u64;
    for (slot, &faulty) in fault_slots.iter().enumerate() {
        for (seed, candidate) in index.seeds.iter().enumerate() {
            if !candidate.broadcast || faulty != Some(candidate.tid) {
                active |= 1u64 << (slot * count + seed);
            }
        }
    }
    let block = (1u64 << count) - 1;
    let faulty_lanes: [u64; NODES] = std::array::from_fn(|tid| block << ((tid + 1) * count));
    let progress = |step: usize| match view.steps[step].kind {
        Kind::Annotation(_) if !matches!(index.roles[step], Role::Boundary) => active,
        Kind::Annotation(_) => active & !faulty_lanes[view.steps[step].tid],
        Kind::Event(event) if view.graph.label(event).is_send() => {
            active & !faulty_lanes[event.tid]
        }
        Kind::Event(_) => 0,
    };
    let mut edges = vec![Edges::default(); view.steps.len()];
    let mut forbidden = vec![0u64; view.steps.len()];
    let mut masks = vec![0u64; view.steps.len()];
    let mut queued = vec![false; view.steps.len()];
    let mut queue = VecDeque::with_capacity(view.steps.len());
    for row in &view.rows {
        if let Some(&first) = row.first() {
            add_lanes(first, progress(first), &mut masks, &mut queued, &mut queue);
        }
        for pair in row.windows(2) {
            edges[pair[1]].add(pair[0], active);
            edges[pair[0]].add(pair[1], progress(pair[1]));
        }
    }
    for (event, step) in view.events() {
        match view.graph.label(event) {
            must::Label::Recv { .. } => {
                edges[step].add(
                    view.event_step(view.graph.reads_from(event).unwrap()),
                    active,
                );
            }
            must::Label::Send { dst, .. } if *dst < NODES => {
                let lanes = active & !faulty_lanes[event.tid] & !faulty_lanes[*dst];
                if let Some(recv) = view.reader(event) {
                    edges[step].add(view.event_step(recv), lanes);
                } else {
                    forbidden[step] = lanes;
                }
            }
            _ => {}
        }
    }
    for (slot, _) in fault_slots.iter().enumerate() {
        for (seed, candidate) in index.seeds.iter().enumerate() {
            add_lanes(
                candidate.step,
                active & (1u64 << (slot * count + seed)),
                &mut masks,
                &mut queued,
                &mut queue,
            );
        }
    }
    // A lane is an independent least Horn closure. OR propagation shares only
    // graph traversal; it cannot add another witness's events to that lane.
    while let Some(step) = queue.pop_front() {
        queued[step] = false;
        for edge in &edges[step].entries[..edges[step].len] {
            add_lanes(
                edge.target,
                masks[step] & edge.lanes,
                &mut masks,
                &mut queued,
                &mut queue,
            );
        }
    }
    let bad = masks
        .iter()
        .zip(&forbidden)
        .fold(0, |bad, (&included, &banned)| bad | (included & banned));
    let delivered: [[u64; NODES]; MESSAGES.len()] = std::array::from_fn(|message| {
        std::array::from_fn(|tid| {
            index.deliveries[message][tid]
                .iter()
                .fold(0, |bits, &step| bits | masks[step])
        })
    });
    // With positive Horn implications, excluding a target delivery succeeds
    // exactly when the unexcluded least closure contains no such delivery.
    for (slot, &faulty) in fault_slots.iter().enumerate() {
        for (seed, candidate) in index.seeds.iter().enumerate() {
            let lane = 1u64 << (slot * count + seed);
            if lane & active & !bad == 0 {
                continue;
            }
            for (target, &target_deliveries) in delivered[candidate.message].iter().enumerate() {
                if (candidate.broadcast && target != candidate.tid)
                    || (!candidate.broadcast && faulty == Some(target))
                    || target_deliveries & lane != 0
                {
                    continue;
                }
                let mut positions = [0; NODES];
                let mut labels = Vec::new();
                for (step, action) in view.steps.iter().enumerate() {
                    if masks[step] & lane != 0 {
                        match action.kind {
                            Kind::Event(_) => positions[action.tid] += 1,
                            Kind::Annotation(label) => labels.push(view.labels[label].clone()),
                        }
                    }
                }
                return Some(CutDiagnostic {
                    faulty,
                    property: if candidate.broadcast {
                        "validity"
                    } else {
                        "uniform agreement"
                    },
                    message: MESSAGES[candidate.message],
                    target,
                    positions,
                    labels,
                });
            }
        }
    }
    None
}

#[cfg(test)]
fn analyze_slow_parts(
    graph: &must::ExecutionGraph,
    labels: &[must::TraceLabel],
) -> Result<Option<CutDiagnostic>, String> {
    let view = View::new(graph, labels)?;
    Ok(analyze_slow_view(&view))
}

#[cfg(test)]
fn analyze_slow_view(view: &View<'_>) -> Option<CutDiagnostic> {
    for faulty in std::iter::once(None).chain((0..NODES).map(Some)) {
        let horn = Horn::new(view, faulty);
        for message in 0..MESSAGES.len() {
            for (seed, step) in view.steps.iter().enumerate() {
                let Some(label) = view.annotation(seed) else {
                    continue;
                };
                let value = must::intern::resolve(label.value);
                let (property, targets): (&'static str, Vec<usize>) =
                    if value == BROADCAST[message] && faulty != Some(step.tid) {
                        ("validity", vec![step.tid])
                    } else if value == DELIVERED[message] {
                        (
                            "uniform agreement",
                            (0..NODES).filter(|&tid| faulty != Some(tid)).collect(),
                        )
                    } else {
                        continue;
                    };
                for target in targets {
                    let excluded: Vec<_> = view.rows[target]
                        .iter()
                        .copied()
                        .filter(|&index| {
                            view.annotation(index).is_some_and(|label| {
                                must::intern::resolve(label.value) == DELIVERED[message]
                            })
                        })
                        .collect();
                    let Some(included) = horn.closure(seed, &excluded) else {
                        continue;
                    };
                    let mut positions = [0; NODES];
                    let mut kept_labels = Vec::new();
                    for (index, step) in view.steps.iter().enumerate() {
                        if included[index] {
                            match step.kind {
                                Kind::Event(_) => positions[step.tid] += 1,
                                Kind::Annotation(label) => {
                                    kept_labels.push(view.labels[label].clone())
                                }
                            }
                        }
                    }
                    return Some(CutDiagnostic {
                        faulty,
                        property,
                        message: MESSAGES[message],
                        target,
                        positions,
                        labels: kept_labels,
                    });
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    // Independent exhaustive prefix tuples: no Horn edges or closure calls.
    fn brute(view: &View<'_>) -> bool {
        for faulty in std::iter::once(None).chain((0..NODES).map(Some)) {
            for a in 0..=view.rows[0].len() {
                for b in 0..=view.rows[1].len() {
                    for c in 0..=view.rows[2].len() {
                        let lengths = [a, b, c];
                        let mut included = vec![false; view.steps.len()];
                        for tid in 0..NODES {
                            for &step in &view.rows[tid][..lengths[tid]] {
                                included[step] = true;
                            }
                        }
                        let mut valid = true;
                        for tid in 0..NODES {
                            if let Some(&next) = view.rows[tid].get(lengths[tid]) {
                                valid &= match view.steps[next].kind {
                                    Kind::Annotation(label) => {
                                        faulty == Some(tid)
                                            && must::intern::resolve(view.labels[label].value)
                                                == BOUNDARY
                                    }
                                    Kind::Event(event) => {
                                        faulty == Some(tid) || view.graph.label(event).is_recv()
                                    }
                                };
                            }
                        }
                        for (event, step) in view.events() {
                            if !included[step] {
                                continue;
                            }
                            match view.graph.label(event) {
                                must::Label::Recv { .. } => {
                                    valid &= included
                                        [view.event_step(view.graph.reads_from(event).unwrap())]
                                }
                                must::Label::Send { dst, .. }
                                    if *dst < NODES
                                        && faulty != Some(event.tid)
                                        && faulty != Some(*dst) =>
                                {
                                    valid &= view
                                        .reader(event)
                                        .is_some_and(|recv| included[view.event_step(recv)]);
                                }
                                _ => {}
                            }
                        }
                        if !valid {
                            continue;
                        }
                        for message in 0..2 {
                            let mut broadcast = [false; NODES];
                            let mut delivered = [false; NODES];
                            for (step, &keep) in included.iter().enumerate() {
                                if !keep {
                                    continue;
                                }
                                if let Some(label) = view.annotation(step) {
                                    let value = must::intern::resolve(label.value);
                                    if value == BROADCAST[message] {
                                        broadcast[label.tid] = true;
                                    }
                                    if value == DELIVERED[message] {
                                        delivered[label.tid] = true;
                                    }
                                }
                            }
                            for tid in 0..NODES {
                                if faulty != Some(tid)
                                    && !delivered[tid]
                                    && (broadcast[tid] || delivered.contains(&true))
                                {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        false
    }

    fn selective_tuple_valid(view: &View<'_>, cuts: [usize; NODES], faulty: Option<usize>) -> bool {
        let included = |step: usize| {
            view.rows[view.steps[step].tid][..cuts[view.steps[step].tid]].contains(&step)
        };
        for tid in 0..NODES {
            if view.rows[tid]
                .get(cuts[tid])
                .is_some_and(|&step| view.progresses(step, faulty))
            {
                return false;
            }
        }
        for (event, step) in view.events() {
            if !included(step) {
                continue;
            }
            match view.graph.label(event) {
                must::Label::Recv { .. } => {
                    if !included(view.event_step(view.graph.reads_from(event).unwrap())) {
                        return false;
                    }
                }
                must::Label::Send { dst, val, .. }
                    if *dst < NODES && faulty != Some(event.tid) && faulty != Some(*dst) =>
                {
                    if view
                        .reader(event)
                        .is_some_and(|reader| included(view.event_step(reader)))
                    {
                        continue;
                    }
                    if let Some(&next) = view.rows[*dst].get(cuts[*dst]) {
                        if let Kind::Event(receive) = view.steps[next].kind {
                            if view
                                .graph
                                .label(receive)
                                .pred()
                                .is_some_and(|pred| pred.test_sym(*val))
                            {
                                return false;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        true
    }

    fn compare_selective_closures(graph: &must::ExecutionGraph, labels: &[must::TraceLabel]) {
        assert!(must::consistency::consistent(graph));
        let view = View::build(graph, labels, true).unwrap();
        let solver = SelectiveCuts::new(&view);
        for faulty in std::iter::once(None).chain((0..NODES).map(Some)) {
            for seed in 0..view.steps.len() {
                let least = solver.closure(faulty, seed);
                assert!(selective_tuple_valid(&view, least, faulty));
                for a in 0..=view.rows[0].len() {
                    for b in 0..=view.rows[1].len() {
                        for c in 0..=view.rows[2].len() {
                            let cuts = [a, b, c];
                            if !view.rows[view.steps[seed].tid][..cuts[view.steps[seed].tid]]
                                .contains(&seed)
                                || !selective_tuple_valid(&view, cuts, faulty)
                            {
                                continue;
                            }
                            assert!((0..NODES).all(|tid| least[tid] <= cuts[tid]));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn selective_closure_matches_prefix_enumeration_with_changing_predicates() {
        for mask in 0..16 {
            let mut graph = must::ExecutionGraph::new();
            let ack = graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "ack"));
            let unlock = graph.add_event(2, must::Label::send(must::Model::Asyn, 1, "unlock"));
            let extra = graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "extra"));
            let first = graph.add_event(
                1,
                must::Label::recv(must::Pred::new("unlock", move |value| {
                    value == "unlock"
                        || (value == "ack" && mask & 1 != 0)
                        || (value == "extra" && mask & 2 != 0)
                })),
            );
            graph.set_rf(first, Some(unlock));
            let second = graph.add_event(
                1,
                must::Label::recv(must::Pred::new("ack", move |value| {
                    value == "ack"
                        || (value == "unlock" && mask & 4 != 0)
                        || (value == "extra" && mask & 8 != 0)
                })),
            );
            graph.set_rf(second, Some(ack));
            let last = graph.add_event(1, must::Label::recv(must::Pred::any()));
            graph.set_rf(last, Some(extra));
            let labels = [
                label(0, 0, BROADCAST[0]),
                label(0, 2, DELIVERED[0]),
                label(1, 2, DELIVERED[0]),
                label(2, 0, BOUNDARY),
            ];
            compare_selective_closures(&graph, &labels);
            let view = View::build(&graph, &labels, true).unwrap();
            let solver = SelectiveCuts::new(&view);
            let seed = view.rows[0]
                .iter()
                .copied()
                .find(|&step| {
                    view.annotation(step).is_some_and(|annotation| {
                        annotation.value == annotation_symbols().deliveries[0]
                    })
                })
                .unwrap();
            let cuts = solver.closure(Some(2), seed);
            assert_eq!(cuts[1] == 0, mask & 3 == 0);
        }
    }

    #[test]
    fn selective_acceptance_is_cached_across_seeds_and_failures() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;

        let calls = Arc::new(AtomicUsize::new(0));
        let count = calls.clone();
        let mut graph = must::ExecutionGraph::new();
        graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "ignored"));
        let accepted = graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "accepted"));
        let receive = graph.add_event(
            1,
            must::Label::recv(must::Pred::new("accepted", move |value| {
                count.fetch_add(1, Ordering::Relaxed);
                value == "accepted"
            })),
        );
        graph.set_rf(receive, Some(accepted));
        let view = View::build(&graph, &[], true).unwrap();
        let solver = SelectiveCuts::new(&view);
        for _ in 0..3 {
            for faulty in std::iter::once(None).chain((0..NODES).map(Some)) {
                for seed in 0..view.steps.len() {
                    solver.closure(faulty, seed);
                }
            }
        }
        assert_eq!(calls.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn discarded_unread_message_does_not_hide_a_terminal_validity_failure() {
        let mut graph = must::ExecutionGraph::new();
        graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "discarded"));
        // Node 1's terminal predicate rejects the packet without committing a receive.
        let labels = [label(0, 0, BROADCAST[0])];
        compare_selective_closures(&graph, &labels);
        let failure = analyze_graph(&graph, &labels).unwrap().unwrap();
        assert_eq!(failure.property, "validity");
        assert_eq!(failure.faulty, None);
        assert_eq!(failure.positions, [1, 0, 0]);
    }

    fn label(tid: usize, position: usize, value: &str) -> must::TraceLabel {
        must::TraceLabel {
            tid,
            position,
            value: value.into(),
        }
    }

    fn compare(graph: &must::ExecutionGraph, labels: &[must::TraceLabel]) {
        let view = View::new(graph, labels).unwrap();
        let fast = analyze_parts(graph, labels).unwrap();
        let slow = analyze_slow_parts(graph, labels).unwrap();
        let trusted = analyze_view(&View::trusted(graph, labels).unwrap());
        assert_eq!(
            fast.as_ref().map(ToString::to_string),
            slow.as_ref().map(ToString::to_string)
        );
        assert_eq!(
            fast.as_ref().map(ToString::to_string),
            trusted.as_ref().map(ToString::to_string)
        );
        assert_eq!(fast.is_some(), brute(&view));
    }

    #[test]
    fn witness_lane_limit_and_fallback_preserve_the_exact_diagnostic() {
        let graph = must::ExecutionGraph::new();
        for count in [0, 1, 8, 16, 17, 32] {
            let labels: Vec<_> = (0..count).map(|_| label(0, 0, DELIVERED[0])).collect();
            compare(&graph, &labels);
            let view = View::new(&graph, &labels).unwrap();
            assert_eq!(AnnotationIndex::new(&view).seeds.len(), count);
        }
    }

    #[test]
    fn more_than_sixty_four_graph_steps_do_not_limit_witness_lanes() {
        let mut graph = direct();
        for _ in 0..65 {
            graph.add_event(0, must::Label::send(must::Model::Asyn, NODES, "sink"));
        }
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 67, DELIVERED[0]),
            label(1, 1, DELIVERED[0]),
            label(2, 1, DELIVERED[0]),
        ];
        assert!(View::new(&graph, &labels).unwrap().steps.len() > 64);
        compare(&graph, &labels);
    }

    fn direct() -> must::ExecutionGraph {
        let mut graph = must::ExecutionGraph::new();
        let first = graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "first"));
        let second = graph.add_event(0, must::Label::send(must::Model::Asyn, 2, "first"));
        let recv = graph.add_event(1, must::Label::recv(must::Pred::any()));
        graph.set_rf(recv, Some(first));
        let recv = graph.add_event(2, must::Label::recv(must::Pred::any()));
        graph.set_rf(recv, Some(second));
        graph
    }

    #[test]
    fn direct_partial_callback_loss_matches_brute_prefixes() {
        let graph = direct();
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 2, DELIVERED[0]),
            label(1, 1, DELIVERED[0]),
            label(2, 1, DELIVERED[0]),
        ];
        compare(&graph, &labels);
        assert!(analyze_parts(&graph, &labels).unwrap().is_some());
    }

    #[test]
    fn complete_flooding_keeps_agreement_under_one_crash() {
        let mut graph = must::ExecutionGraph::new();
        let mut sends = BTreeMap::new();
        for destination in [1, 2] {
            sends.insert(
                (0, destination),
                graph.add_event(
                    0,
                    must::Label::send(must::Model::Asyn, destination, "first"),
                ),
            );
        }
        for tid in [1, 2] {
            let recv = graph.add_event(tid, must::Label::recv(must::Pred::any()));
            graph.set_rf(recv, Some(sends[&(0, tid)]));
            for destination in 0..NODES {
                if destination != tid {
                    sends.insert(
                        (tid, destination),
                        graph.add_event(
                            tid,
                            must::Label::send(must::Model::Asyn, destination, "first"),
                        ),
                    );
                }
            }
        }
        for (source, destination) in [(1, 0), (2, 0), (2, 1), (1, 2)] {
            let recv = graph.add_event(destination, must::Label::recv(must::Pred::any()));
            graph.set_rf(recv, Some(sends[&(source, destination)]));
        }
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 3, DELIVERED[0]),
            label(1, 3, DELIVERED[0]),
            label(2, 3, DELIVERED[0]),
        ];
        compare(&graph, &labels);
        assert!(analyze_parts(&graph, &labels).unwrap().is_none());
    }

    #[test]
    fn faulty_annotations_after_last_committed_event_are_mandatory() {
        let mut graph = must::ExecutionGraph::new();
        let send = graph.add_event(1, must::Label::send(must::Model::Asyn, 2, "first"));
        let recv = graph.add_event(2, must::Label::recv(must::Pred::any()));
        graph.set_rf(recv, Some(send));
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 0, DELIVERED[0]),
            label(1, 0, DELIVERED[0]),
            label(2, 1, DELIVERED[0]),
        ];
        compare(&graph, &labels);
        let view = View::new(&graph, &labels).unwrap();
        let initial = view.rows[1][0];
        assert!(Horn::new(&view, Some(1))
            .closure(view.rows[0][0], &[initial])
            .is_none());
        let receive = view.event_step(recv);
        let after_receive = *view.rows[2].last().unwrap();
        assert!(Horn::new(&view, Some(2))
            .closure(receive, &[after_receive])
            .is_none());
    }

    #[test]
    fn same_position_order_and_explicit_input_crash_boundary_match_brute() {
        let graph = direct();
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 0, DELIVERED[0]),
            label(0, 0, BOUNDARY),
            label(0, 0, BROADCAST[1]),
            label(0, 0, DELIVERED[1]),
            label(1, 1, DELIVERED[0]),
            label(1, 1, DELIVERED[1]),
            label(2, 1, DELIVERED[0]),
            label(2, 1, DELIVERED[1]),
        ];
        compare(&graph, &labels);
        let view = View::new(&graph, &labels).unwrap();
        let second_broadcast = view.rows[0][3];
        assert!(Horn::new(&view, Some(0))
            .closure(view.rows[0][0], &[second_broadcast])
            .is_some());
    }

    #[test]
    fn receive_prefixes_and_sink_sends_match_brute() {
        let mut graph = direct();
        let send = graph.add_event(1, must::Label::send(must::Model::Asyn, 0, "ack"));
        graph.add_event(1, must::Label::send(must::Model::Asyn, NODES, "sink"));
        let recv = graph.add_event(0, must::Label::recv(must::Pred::any()));
        graph.set_rf(recv, Some(send));
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 3, DELIVERED[0]),
            label(1, 1, DELIVERED[0]),
            label(2, 1, DELIVERED[0]),
        ];
        compare(&graph, &labels);
    }

    #[test]
    fn unsupported_events_and_selective_predicates_fail_closed() {
        let mut graph = must::ExecutionGraph::new();
        graph.add_event(0, must::Label::nondet(["one", "two"]));
        assert!(analyze_parts(&graph, &[]).is_err());
        let mut graph = must::ExecutionGraph::new();
        let send = graph.add_event(0, must::Label::send(must::Model::P2p, 1, "first"));
        let recv = graph.add_event(1, must::Label::recv(must::Pred::any()));
        graph.set_rf(recv, Some(send));
        assert!(analyze_parts(&graph, &[]).is_err());
        // A printable tag cannot spoof constructor-proven recv_any semantics.
        let mut selective = must::ExecutionGraph::new();
        let send = selective.add_event(0, must::Label::send(must::Model::Asyn, 1, "first"));
        selective.add_event(0, must::Label::send(must::Model::Asyn, 1, "rejected"));
        let recv = selective.add_event(
            1,
            must::Label::recv(must::Pred::new("true", |value| value == "first")),
        );
        selective.set_rf(recv, Some(send));
        assert!(analyze_parts(&selective, &[]).is_err());
    }

    #[test]
    fn trusted_path_keeps_missing_and_duplicate_source_guards() {
        let mut graph = must::ExecutionGraph::new();
        graph.add_event(1, must::Label::recv(must::Pred::any()));
        assert!(View::trusted(&graph, &[]).is_err());
        assert!(analyze_prefix(&graph, &[]).is_err());
        let mut graph = must::ExecutionGraph::new();
        let send = graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "first"));
        for _ in 0..2 {
            let recv = graph.add_event(1, must::Label::recv(must::Pred::any()));
            graph.set_rf(recv, Some(send));
        }
        assert!(View::trusted(&graph, &[]).is_err());
        assert!(analyze_prefix(&graph, &[]).is_err());
    }

    #[test]
    fn prefix_closure_matches_references_across_annotation_boundaries() {
        let graph = direct();
        for first_delivery in 0..=2 {
            for second_input in 0..=2 {
                for receiver_one in 0..=1 {
                    for receiver_two in 0..=1 {
                        let mut labels = vec![
                            label(0, 0, BROADCAST[0]),
                            label(0, first_delivery, DELIVERED[0]),
                            label(0, second_input, BOUNDARY),
                            label(0, second_input, BROADCAST[1]),
                            label(0, 2, DELIVERED[1]),
                            label(1, receiver_one, DELIVERED[0]),
                            label(1, 1, DELIVERED[1]),
                            label(2, receiver_two, DELIVERED[0]),
                            label(2, 1, DELIVERED[1]),
                        ];
                        labels.sort_by_key(|label| (label.tid, label.position));
                        compare(&graph, &labels);
                    }
                }
            }
        }
    }

    fn flood_with_receive_tail() -> (must::ExecutionGraph, Vec<must::TraceLabel>) {
        let mut graph = must::ExecutionGraph::new();
        let to_one = graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "first"));
        let to_two = graph.add_event(0, must::Label::send(must::Model::Asyn, 2, "first"));
        let receive = graph.add_event(1, must::Label::recv(must::Pred::any()));
        graph.set_rf(receive, Some(to_one));
        let one_zero = graph.add_event(1, must::Label::send(must::Model::Asyn, 0, "first"));
        let one_two = graph.add_event(1, must::Label::send(must::Model::Asyn, 2, "first"));
        let extra = graph.add_event(1, must::Label::send(must::Model::Asyn, 0, "first"));
        let receive = graph.add_event(2, must::Label::recv(must::Pred::any()));
        graph.set_rf(receive, Some(to_two));
        let two_zero = graph.add_event(2, must::Label::send(must::Model::Asyn, 0, "first"));
        let two_one = graph.add_event(2, must::Label::send(must::Model::Asyn, 1, "first"));
        for source in [one_zero, extra, two_zero] {
            let receive = graph.add_event(0, must::Label::recv(must::Pred::any()));
            graph.set_rf(receive, Some(source));
        }
        let receive = graph.add_event(1, must::Label::recv(must::Pred::any()));
        graph.set_rf(receive, Some(two_one));
        let receive = graph.add_event(2, must::Label::recv(must::Pred::any()));
        graph.set_rf(receive, Some(one_two));
        let labels = vec![
            label(0, 0, BROADCAST[0]),
            label(0, 3, DELIVERED[0]),
            label(1, 3, DELIVERED[0]),
            label(2, 3, DELIVERED[0]),
        ];
        (graph, labels)
    }

    #[test]
    fn projected_pass_reuses_exact_key_across_receive_tail_permutations() {
        let (graph, labels) = flood_with_receive_tail();
        let mut swapped = graph.clone();
        swapped.set_rf(must::EventId::new(0, 3), Some(must::EventId::new(2, 1)));
        swapped.set_rf(must::EventId::new(0, 4), Some(must::EventId::new(1, 3)));
        compare(&graph, &labels);
        compare(&swapped, &labels);
        assert!(analyze_slow_parts(&graph, &labels).unwrap().is_none());
        let mut workspace = PrefixWorkspace::default();
        assert!(analyze_cached(&mut workspace, &graph, &labels)
            .unwrap()
            .is_none());
        assert_eq!(workspace.pass_cache.certificates, 1);
        assert!(analyze_cached(&mut workspace, &swapped, &labels)
            .unwrap()
            .is_none());
        assert_eq!(workspace.pass_cache.hits, 1);
        // Hand-built graphs have no program metadata: structural keys are a
        // complete fallback, with no replay-token assumptions.
        assert!(graph.program_prefix_identity(0, 3).is_none());
    }

    #[test]
    fn projected_unknown_falls_back_and_never_caches_counterexamples() {
        let graph = direct();
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 2, DELIVERED[0]),
            label(1, 1, DELIVERED[0]),
            label(2, 1, DELIVERED[0]),
        ];
        let expected = analyze_slow_parts(&graph, &labels)
            .unwrap()
            .unwrap()
            .to_string();
        let mut workspace = PrefixWorkspace::default();
        for _ in 0..2 {
            assert_eq!(
                analyze_cached(&mut workspace, &graph, &labels)
                    .unwrap()
                    .unwrap()
                    .to_string(),
                expected
            );
        }
        assert_eq!(workspace.pass_cache.fallbacks, 2);
        assert_eq!(workspace.pass_cache.certificates, 0);
        assert_eq!(workspace.pass_cache.hits, 0);
    }

    #[test]
    fn pass_cache_hash_collision_requires_exact_key_equality() {
        let mut cache = PassCache::default();
        cache.insert(&[1, 2, 3], 17);
        assert!(cache.contains(&[1, 2, 3], 17));
        assert!(!cache.contains(&[1, 2, 4], 17));
        cache.insert(&[1, 2, 4], 17);
        assert!(!cache.contains(&[1, 2, 3], 17));
        assert!(cache.contains(&[1, 2, 4], 17));
    }

    #[test]
    fn unsupported_tail_is_checked_before_a_pass_cache_hit() {
        let (graph, labels) = flood_with_receive_tail();
        let mut workspace = PrefixWorkspace::default();
        assert!(analyze_cached(&mut workspace, &graph, &labels)
            .unwrap()
            .is_none());
        let mut unsupported = graph.clone();
        unsupported.add_event(0, must::Label::nondet(["one", "two"]));
        assert!(analyze_cached(&mut workspace, &unsupported, &labels).is_err());
        assert_eq!(workspace.pass_cache.hits, 0);
    }

    #[test]
    fn packed_edges_have_an_exact_wide_escape_without_index_limits() {
        let mut key = Vec::new();
        let largest = u64::MAX >> 3;
        append_packed(&mut key, 5, largest);
        assert_eq!(key, vec![(largest << 3) | 5]);
        assert_ne!(key[0], u64::MAX);
        append_packed(&mut key, 2, u64::MAX);
        assert_eq!(&key[1..], &[u64::MAX, 2, u64::MAX]);
    }

    #[test]
    fn metadata_compact_key_matches_horn_with_certified_and_checked_paths() {
        let observer = must::ExecutionCollector::default();
        must::explore(
            || {
                let mut system = must::System::new();
                system.add(|ctx| async move {
                    ctx.insert_label(BROADCAST[0]);
                    ctx.send(1, "first", must::Model::Asyn);
                    ctx.send(2, "first", must::Model::Asyn);
                    ctx.recv_any().await;
                    ctx.insert_label(DELIVERED[0]);
                    ctx.recv_any().await;
                    ctx.recv_any().await;
                });
                system.add(|ctx| async move {
                    ctx.recv_any().await;
                    ctx.send(0, "first", must::Model::Asyn);
                    ctx.send(2, "first", must::Model::Asyn);
                    ctx.insert_label(DELIVERED[0]);
                    ctx.send(0, "first", must::Model::Asyn);
                    ctx.recv_any().await;
                });
                system.add(|ctx| async move {
                    ctx.recv_any().await;
                    ctx.send(0, "first", must::Model::Asyn);
                    ctx.send(1, "first", must::Model::Asyn);
                    ctx.insert_label(DELIVERED[0]);
                    ctx.recv_any().await;
                });
                system
            },
            &observer,
            must::Config::default().with_threads(1),
        );
        let mut checked = PrefixWorkspace::default();
        let mut certified = PrefixWorkspace::default();
        let mut compact_seen = false;
        let executions = observer.terminals();
        assert!(!executions.is_empty());
        for execution in executions {
            let graph = execution.graph();
            let labels = execution.labels();
            let expected = analyze_slow_parts(graph, labels)
                .unwrap()
                .as_ref()
                .map(ToString::to_string);
            let result = analyze_cached(&mut checked, graph, labels).unwrap();
            assert_eq!(result.as_ref().map(ToString::to_string), expected);
            let result = analyze_cached_mode(&mut certified, graph, labels, true, false).unwrap();
            assert_eq!(result.as_ref().map(ToString::to_string), expected);
            assert_eq!(checked.key.first(), Some(&0));
            compact_seen |= certified.key.first() == Some(&1);
        }
        assert!(
            compact_seen,
            "runtime histories must exercise compact token keys"
        );
    }

    #[test]
    fn no_creation_checks_local_order_and_the_actual_rf_path() {
        let graph = must::ExecutionGraph::new();
        assert!(check_creation(&graph, &[label(0, 0, DELIVERED[0])]).is_some());
        assert!(check_creation(
            &graph,
            &[label(0, 0, DELIVERED[0]), label(0, 0, BROADCAST[0])]
        )
        .is_some());
        assert!(check_creation(
            &graph,
            &[label(0, 0, BROADCAST[0]), label(0, 0, DELIVERED[0])]
        )
        .is_none());
        let graph = direct();
        let valid = [label(0, 0, BROADCAST[0]), label(1, 1, DELIVERED[0])];
        assert!(check_creation(&graph, &valid).is_none());
        // The input exists, but comes after the source send read by node 1.
        let invented_before_input = [label(0, 1, BROADCAST[0]), label(1, 1, DELIVERED[0])];
        let failure = check_creation(&graph, &invented_before_input).unwrap();
        assert_eq!(failure.property, "no creation");
        assert_eq!(failure.target, 1);
    }

    #[test]
    fn liveness_pass_cache_cannot_skip_combined_creation_checks() {
        let graph = must::ExecutionGraph::new();
        let labels = [
            label(0, 0, DELIVERED[0]),
            label(1, 0, DELIVERED[0]),
            label(2, 0, DELIVERED[0]),
        ];
        let mut workspace = PrefixWorkspace::default();
        assert!(analyze_cached(&mut workspace, &graph, &labels)
            .unwrap()
            .is_none());
        assert_eq!(workspace.pass_cache.certificates, 1);
        for _ in 0..2 {
            let failure = analyze_cached_mode(&mut workspace, &graph, &labels, false, true)
                .unwrap()
                .unwrap();
            assert_eq!(failure.property, "no creation");
        }
        assert_eq!(workspace.pass_cache.hits, 0);
        assert_eq!(workspace.pass_cache.certificates, 1);
    }

    #[test]
    fn combined_pass_certificate_survives_receive_tail_permutations() {
        let (graph, labels) = flood_with_receive_tail();
        let mut swapped = graph.clone();
        swapped.set_rf(must::EventId::new(0, 3), Some(must::EventId::new(2, 1)));
        swapped.set_rf(must::EventId::new(0, 4), Some(must::EventId::new(1, 3)));
        assert!(check_creation(&graph, &labels).is_none());
        assert!(check_creation(&swapped, &labels).is_none());
        let mut workspace = PrefixWorkspace::default();
        assert!(
            analyze_cached_mode(&mut workspace, &graph, &labels, false, true)
                .unwrap()
                .is_none()
        );
        assert!(
            analyze_cached_mode(&mut workspace, &swapped, &labels, false, true)
                .unwrap()
                .is_none()
        );
        assert_eq!(workspace.pass_cache.certificates, 1);
        assert_eq!(workspace.pass_cache.hits, 1);
    }

    fn pending_by_destination(graph: &must::ExecutionGraph) -> Vec<Vec<must::EventId>> {
        let mut pending = vec![Vec::new(); NODES];
        for send in graph.unread_sends() {
            let destination = graph.label(send).dst().unwrap();
            if destination < NODES {
                pending[destination].push(send);
            }
        }
        pending
    }

    #[test]
    fn completed_tail_prefix_pass_matches_every_terminal_permutation() {
        let (full, labels) = flood_with_receive_tail();
        let caps = [3, 4, 3];
        let keep = full
            .all_events()
            .into_iter()
            .filter(|event| event.idx < caps[event.tid])
            .collect();
        let prefix = full.restrict(&keep);
        let pending = pending_by_destination(&prefix);
        assert_eq!(pending[0].len(), 2);
        let mut workspace = PrefixWorkspace::default();
        assert!(prove_tail_cached(&mut workspace, &prefix, &labels, &pending, true).unwrap());
        assert_eq!(workspace.pass_cache.certificates, 1);
        assert!(prove_tail_cached(&mut workspace, &prefix, &labels, &pending, true).unwrap());
        assert_eq!(workspace.pass_cache.hits, 1);
        for reverse in [false, true] {
            let mut completed = prefix.clone();
            for (destination, sends) in pending.iter().enumerate() {
                let mut sends = sends.clone();
                if reverse {
                    sends.reverse();
                }
                for send in sends {
                    let receive =
                        completed.add_event(destination, must::Label::recv(must::Pred::any()));
                    completed.set_rf(receive, Some(send));
                }
            }
            assert!(check_creation(&completed, &labels).is_none());
            assert!(analyze_slow_parts(&completed, &labels).unwrap().is_none());
        }
    }

    #[test]
    fn tail_binding_does_not_reuse_ordinary_unread_forbidden_pass() {
        let mut graph = must::ExecutionGraph::new();
        let zero_one = graph.add_event(0, must::Label::send(must::Model::Asyn, 1, "first"));
        graph.add_event(0, must::Label::send(must::Model::Asyn, 2, "first"));
        let receive = graph.add_event(1, must::Label::recv(must::Pred::any()));
        graph.set_rf(receive, Some(zero_one));
        let acknowledgement = graph.add_event(1, must::Label::send(must::Model::Asyn, 0, "first"));
        graph.add_event(1, must::Label::send(must::Model::Asyn, 2, "first"));
        let receive = graph.add_event(0, must::Label::recv(must::Pred::any()));
        graph.set_rf(receive, Some(acknowledgement));
        let labels = [
            label(0, 0, BROADCAST[0]),
            label(0, 3, DELIVERED[0]),
            label(1, 3, DELIVERED[0]),
        ];
        let pending = pending_by_destination(&graph);
        let mut workspace = PrefixWorkspace::default();
        // Ordinary terminal analysis forbids live unread sends. This graph is
        // a prefix, and only tail mode may reason about their future delivery.
        assert!(analyze_cached(&mut workspace, &graph, &labels)
            .unwrap()
            .is_none());
        let ordinary_key = workspace.key.clone();
        assert!(!prove_tail_cached(&mut workspace, &graph, &labels, &pending, false).unwrap());
        assert_ne!(ordinary_key, workspace.key);
        assert_eq!(workspace.pass_cache.hits, 0);
        assert_eq!(workspace.pass_cache.certificates, 1);
        let mut completed = graph.clone();
        for send in &pending[2] {
            let receive = completed.add_event(2, must::Label::recv(must::Pred::any()));
            completed.set_rf(receive, Some(*send));
        }
        assert!(analyze_slow_parts(&completed, &labels).unwrap().is_some());
    }

    #[test]
    fn tail_pending_binding_rejects_omissions_duplicates_and_read_sends() {
        let (full, labels) = flood_with_receive_tail();
        let caps = [3, 4, 3];
        let keep = full
            .all_events()
            .into_iter()
            .filter(|event| event.idx < caps[event.tid])
            .collect();
        let prefix = full.restrict(&keep);
        let pending = pending_by_destination(&prefix);
        let mut workspace = PrefixWorkspace::default();
        let mut missing = pending.clone();
        missing[0].pop();
        assert!(prove_tail_cached(&mut workspace, &prefix, &labels, &missing, false).is_err());
        let mut duplicate = pending.clone();
        let duplicate_send = duplicate[0][0];
        duplicate[0].push(duplicate_send);
        assert!(prove_tail_cached(&mut workspace, &prefix, &labels, &duplicate, false).is_err());
        let mut read = pending;
        read[1].push(must::EventId::new(0, 0));
        assert!(prove_tail_cached(&mut workspace, &prefix, &labels, &read, false).is_err());
    }
}
