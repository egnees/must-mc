//! Directed ownership audit. A viable oracle witness is not itself a canonical owner.
//! Compare exact terminal sets separately from the local, conditional transplant lemma.

mod common;
mod hunt_common;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use hunt_common::{Op, Sel, VdProgram};
use must::time::witness::{query, OracleBudget, OracleOutcome, PinnedChoice};
use must::{
    explore, traces_of, Config, EventId, Execution, ExecutionGraph, ExecutionKind, Label, Model,
    Observer, Program, Val,
};

fn target(g: &ExecutionGraph, r: EventId, s: EventId) -> ExecutionGraph {
    let ancestors = g.porf_prefix(s);
    let keep = g
        .iter_events()
        .filter(|&e| g.stamp(e) <= g.stamp(r) || ancestors.contains(&e) || e == s)
        .collect();
    let mut result = g.restrict(&keep);
    result.set_rf(r, Some(s));
    result
}

fn extends(g: &ExecutionGraph, prefix: &ExecutionGraph) -> bool {
    prefix.iter_events().all(|e| {
        g.contains(e)
            && g.label(e) == prefix.label(e)
            && g.reads_from(e) == prefix.reads_from(e)
            && g.nd_value(e) == prefix.nd_value(e)
    })
}

fn assert_same_graph(a: &ExecutionGraph, b: &ExecutionGraph) {
    assert_eq!(a.iter_events().count(), b.iter_events().count());
    assert!(
        extends(a, b),
        "event/label/rf/ND mismatch\na={a:?}\nb={b:?}"
    );
    assert_eq!(a.canonical_key(), b.canonical_key());
}

fn same_stamped_graph(a: &ExecutionGraph, b: &ExecutionGraph) -> bool {
    a.num_threads() == b.num_threads()
        && a.iter_events().count() == b.iter_events().count()
        && extends(a, b)
        && a.iter_events().all(|e| a.stamp(e) == b.stamp(e))
}

fn structural_guards(g: &ExecutionGraph, r: EventId, s: EventId) -> bool {
    let ancestors = g.porf_prefix(s);
    g.iter_events()
        .filter(|&e| g.stamp(e) > g.stamp(r) && !ancestors.contains(&e))
        .chain(std::iter::once(r))
        .all(|e| match g.label(e) {
            Label::Send { .. } | Label::Error { .. } => !g.iter_recvs().any(|reader| {
                g.reads_from(reader) == Some(e)
                    && (g.stamp(reader) <= g.stamp(e) || ancestors.contains(&reader))
            }),
            Label::Recv { blocking, .. } => {
                assert!(blocking, "this first audit covers blocking receives");
                true
            }
            Label::Nondet { .. } => true,
        })
}

/// Independent test reconstruction of Previous minus the dependency cone. Every
/// production callback is cross-checked against this before it is used for held values.
fn base_for(g: &ExecutionGraph, ep: EventId, send: EventId) -> ExecutionGraph {
    let protected = g.porf_prefix(send);
    let previous: BTreeSet<_> = g
        .iter_events()
        .filter(|&e| g.stamp(e) <= g.stamp(ep) || protected.contains(&e))
        .collect();
    let mut cut = vec![usize::MAX; g.num_threads()];
    cut[ep.tid] = ep.idx + 1;
    loop {
        let mut changed = false;
        for &reader in &previous {
            if let Some(source) = g.reads_from(reader) {
                if source.idx >= cut[source.tid] && reader.idx < cut[reader.tid] {
                    cut[reader.tid] = reader.idx;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    g.restrict(
        &previous
            .into_iter()
            .filter(|e| e.idx < cut[e.tid])
            .collect(),
    )
}

fn stamped(g: &ExecutionGraph) -> String {
    let mut events: Vec<_> = g.iter_events().collect();
    events.sort_by_key(|&e| g.stamp(e));
    events
        .into_iter()
        .map(|e| {
            format!(
                "  #{} {e} {:?} rf={:?} nd={:?}\n",
                g.stamp(e),
                g.label(e),
                g.reads_from(e),
                g.nd_value(e)
            )
        })
        .collect()
}

#[derive(Default)]
struct Terminals(
    Mutex<BTreeMap<String, ExecutionGraph>>,
    Mutex<usize>,
    Mutex<(usize, Option<Instant>)>,
);

impl Observer for Terminals {
    fn on_visit_enter(&self, _g: &ExecutionGraph) {
        let mut budget = self.2.lock().unwrap();
        budget.0 += 1;
        let started = *budget.1.get_or_insert_with(Instant::now);
        assert!(budget.0 < 20_000, "reference exceeded bounded Visit budget");
        assert!(
            started.elapsed() < Duration::from_secs(30),
            "reference exceeded time budget"
        );
    }

    fn on_execution(&self, exec: &Execution, kind: ExecutionKind) {
        assert_eq!(
            common::time_feasible_ref(exec.graph(), &mut 10_000),
            Some(true),
            "independent finite-delay check must complete and accept each reported graph"
        );
        let key = format!("{kind:?}:{}", exec.canonical_key());
        if self
            .0
            .lock()
            .unwrap()
            .insert(key, exec.graph().clone())
            .is_some()
        {
            *self.1.lock().unwrap() += 1;
        }
    }

    fn on_execution_filtered(&self, exec: &Execution, _kind: ExecutionKind) {
        assert_eq!(
            common::time_feasible_ref(exec.graph(), &mut 10_000),
            Some(false),
            "independent finite-delay check must complete and reject each filtered graph"
        );
    }
}

#[derive(Clone)]
struct Candidate {
    host: ExecutionGraph,
    target: ExecutionGraph,
    victim: EventId,
    send: EventId,
    structural: bool,
    smaller_true: bool,
    witnesses: Vec<ExecutionGraph>,
}

#[derive(Debug, Default)]
struct Counts {
    visits: usize,
    candidates: usize,
    structural_candidates: usize,
    partial_candidates: usize,
    admitted: usize,
    rejected: usize,
    smaller_queries: usize,
    receive_queries: usize,
    smaller_true: usize,
    smaller_false: usize,
    held_queries: usize,
    held_false: usize,
    admitted_held_queries: usize,
    admitted_held_false: usize,
    structural_true_witnesses: usize,
    partial_true_witnesses: usize,
    partial_missing_victim: usize,
    rejected_by_smaller: usize,
    rejected_structural_by_smaller: usize,
    rejected_with_exact_owner: usize,
    rejected_with_visited_target: usize,
    rejected_with_terminal_extension: usize,
    rejected_structural_without_owner: usize,
    witness_hosts_visited: usize,
    oracle_states: usize,
    oracle_additions: usize,
    owner_certificates: usize,
    owner_replay_events: usize,
    owner_certificates_with_actual_owner: usize,
}

#[derive(Default)]
struct AuditState {
    counts: Counts,
    current: Option<Candidate>,
    rejected: Vec<Candidate>,
    admitted: BTreeSet<String>,
    admitted_hosts: Vec<Candidate>,
    certified_owners: Vec<(EventId, EventId, ExecutionGraph, ExecutionGraph)>,
    visited: BTreeSet<String>,
}

struct Audit<'a> {
    program: &'a VdProgram,
    priorities: &'a [usize],
    started: Instant,
    state: Mutex<AuditState>,
}

#[derive(Clone, Copy)]
enum QueryKind {
    Smaller,
    DebugHeld,
    AcceptedHeld,
}

impl Audit<'_> {
    fn inspect(
        &self,
        base: &ExecutionGraph,
        pin: PinnedChoice,
        send: EventId,
        label: &Label,
        expected: Option<bool>,
        kind: QueryKind,
    ) -> bool {
        let mut state = self.state.lock().unwrap();
        let candidate = state
            .current
            .as_ref()
            .expect("query inside a candidate")
            .clone();
        assert_eq!(send, candidate.send);
        let ep = match pin {
            PinnedChoice::Nondet { event, .. } | PinnedChoice::Receive { event, .. } => event,
        };
        assert_same_graph(base, &base_for(&candidate.host, ep, send));
        let protected = candidate.host.porf_prefix(send);
        assert!(!protected.contains(&ep));
        for e in protected {
            assert!(base.contains(e), "protected event {e} erased by {ep}");
            assert_eq!(base.label(e), candidate.host.label(e));
            assert_eq!(base.reads_from(e), candidate.host.reads_from(e));
            assert_eq!(base.nd_value(e), candidate.host.nd_value(e));
        }
        assert!(!base.contains(send));
        assert_eq!(base.thread_len(send.tid), send.idx);
        assert_eq!(
            self.program
                .next_thread(
                    send.tid,
                    &traces_of(base, self.program.num_threads())[send.tid]
                )
                .label(),
            Some(label)
        );
        let result = query(
            base,
            pin,
            self.program,
            self.priorities,
            send,
            label,
            &mut must::time::ViableMemo::default(),
            OracleBudget {
                max_states: 2,
                max_added_events: 100,
            },
        );
        let verdict = result
            .verdict()
            .expect("bounded oracle audit must complete");
        if let Some(expected) = expected {
            assert_eq!(verdict, expected, "diagnostic verdict mismatch");
        }
        let stats = result.stats();
        assert_eq!(
            stats.states, 1,
            "actual canonical call must settle in its initial drain"
        );
        assert!(stats.target_initially_ready);
        assert!(!stats.target_present_on_entry);
        assert_eq!(stats.branch_states, 0);
        assert_eq!(stats.branch_children, 0);
        state.counts.oracle_states += stats.states;
        state.counts.oracle_additions += stats.added_events;
        match kind {
            QueryKind::DebugHeld => {
                state.counts.held_queries += 1;
                state.counts.held_false += usize::from(!verdict);
            }
            QueryKind::AcceptedHeld => {
                state.counts.admitted_held_queries += 1;
                state.counts.admitted_held_false += usize::from(!verdict);
            }
            QueryKind::Smaller => {
                state.counts.smaller_queries += 1;
                state.counts.receive_queries +=
                    usize::from(matches!(pin, PinnedChoice::Receive { .. }));
                state.counts.smaller_true += usize::from(verdict);
                state.counts.smaller_false += usize::from(!verdict);
                state.current.as_mut().unwrap().smaller_true |= verdict;
            }
        }
        if let OracleOutcome::Witness(witness) = result {
            assert!(witness.recheck(self.program));
            let g = witness.graph();
            // The witness's final drain can run past s; cut precisely at s's insertion.
            let through_send = g.restrict(
                &g.iter_events()
                    .filter(|&e| g.stamp(e) <= g.stamp(send))
                    .collect(),
            );
            assert!(must::consistency::consistent(&through_send));
            assert!(must::time::gate_feasible(
                &through_send,
                self.program,
                self.priorities
            ));
            assert!(through_send
                .iter_events()
                .all(|e| g.stamp(e) <= g.stamp(send)));
            if candidate.structural {
                state.counts.structural_true_witnesses += 1;
                assert!(through_send.contains(candidate.victim));
                assert_same_graph(
                    &target(&through_send, candidate.victim, send),
                    &candidate.target,
                );
            } else {
                state.counts.partial_true_witnesses += 1;
                state.counts.partial_missing_victim +=
                    usize::from(!through_send.contains(candidate.victim));
            }
            if matches!(kind, QueryKind::Smaller) {
                state.current.as_mut().unwrap().witnesses.push(through_send);
            }
        }
        verdict
    }
}

impl Observer for Audit<'_> {
    fn on_visit_enter(&self, g: &ExecutionGraph) {
        let mut state = self.state.lock().unwrap();
        state.counts.visits += 1;
        assert!(
            state.counts.visits < 20_000,
            "bounded audit exceeded its Visit limit"
        );
        assert!(
            self.started.elapsed() < Duration::from_secs(30),
            "bounded audit exceeded 30 seconds"
        );
        state.visited.insert(g.canonical_key());
    }

    fn on_revisit_candidate(&self, g: &ExecutionGraph, r: EventId, s: EventId, t: &ExecutionGraph) {
        let mut state = self.state.lock().unwrap();
        assert!(state.current.is_none());
        assert_same_graph(&target(g, r, s), t);
        state.counts.candidates += 1;
        let structural = structural_guards(g, r, s);
        state.counts.structural_candidates += usize::from(structural);
        state.counts.partial_candidates += usize::from(!structural);
        state.current = Some(Candidate {
            host: g.clone(),
            target: t.clone(),
            victim: r,
            send: s,
            structural,
            smaller_true: false,
            witnesses: Vec::new(),
        });
    }

    fn on_revisit_arm_rejected(
        &self,
        _g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        t: &ExecutionGraph,
        _event: EventId,
    ) {
        let mut state = self.state.lock().unwrap();
        let candidate = state.current.take().unwrap();
        assert_eq!((candidate.victim, candidate.send), (r, s));
        assert_same_graph(&candidate.target, t);
        state.counts.rejected += 1;
        state.rejected.push(candidate);
    }

    fn on_revisit_owner_certified(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        owner: &ExecutionGraph,
        replay_events: usize,
    ) {
        let mut state = self.state.lock().unwrap();
        let candidate = state.current.as_ref().unwrap().clone();
        assert_eq!((candidate.victim, candidate.send), (r, s));
        assert!(same_stamped_graph(g, &candidate.host));
        assert!(candidate.structural);
        assert!(!candidate.smaller_true);
        assert_eq!(replay_events, owner.iter_events().count());
        assert!(replay_events <= 256);
        assert!(g.iter_events().all(|e| owner.contains(e)
            && g.label(e) == owner.label(e)
            && g.stamp(e) == owner.stamp(e)));
        assert!(same_stamped_graph(&target(owner, r, s), &candidate.target));
        assert!(structural_guards(owner, r, s));
        let ancestors = owner.porf_prefix(s);
        let previous = owner.restrict(
            &owner
                .iter_events()
                .filter(|&e| owner.stamp(e) <= owner.stamp(r) || ancestors.contains(&e))
                .collect(),
        );
        assert_eq!(
            owner.reads_from(r),
            must::explorer::revisit::get_cons_tiebreaker(&previous, r, true)
        );
        for e in owner
            .iter_events()
            .filter(|&e| owner.stamp(e) > owner.stamp(r) && !ancestors.contains(&e) && e != s)
        {
            let Label::Nondet { set } = owner.label(e) else {
                panic!("unsupported deleted event in certified owner");
            };
            let minimum = set.iter().min_by_key(|&&v| must::intern::resolve(v));
            assert_eq!(owner.nd_value(e), minimum);
        }
        state.counts.owner_certificates += 1;
        state.counts.owner_replay_events += replay_events;
        state
            .certified_owners
            .push((r, s, owner.clone(), candidate.target));
    }

    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        _deleted: &BTreeSet<EventId>,
    ) {
        let protected = g.porf_prefix(s);
        for ep in g
            .iter_events()
            .filter(|&e| g.stamp(e) > g.stamp(r) && !protected.contains(&e))
            .chain(std::iter::once(r))
        {
            let pin = match g.label(ep) {
                Label::Nondet { .. } => PinnedChoice::Nondet {
                    event: ep,
                    value: *g.nd_value(ep).unwrap(),
                },
                Label::Recv { .. } => PinnedChoice::Receive {
                    event: ep,
                    source: g.reads_from(ep),
                },
                _ => continue,
            };
            self.inspect(
                &base_for(g, ep, s),
                pin,
                s,
                g.label(s),
                None,
                QueryKind::AcceptedHeld,
            );
        }
        let mut state = self.state.lock().unwrap();
        let candidate = state.current.take().unwrap();
        assert_eq!((candidate.victim, candidate.send), (r, s));
        assert!(candidate.structural);
        assert!(!candidate.smaller_true);
        assert_same_graph(&target(g, r, s), &candidate.target);
        state.counts.admitted += 1;
        state.admitted.insert(candidate.target.canonical_key());
        state.admitted_hosts.push(candidate);
    }

    fn on_viable_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        v: Val,
        s: EventId,
        label: &Label,
        verdict: bool,
    ) {
        self.inspect(
            base,
            PinnedChoice::Nondet {
                event: ep,
                value: v,
            },
            s,
            label,
            Some(verdict),
            QueryKind::Smaller,
        );
    }

    fn on_held_viable_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        v: Val,
        s: EventId,
        label: &Label,
        verdict: bool,
    ) {
        self.inspect(
            base,
            PinnedChoice::Nondet {
                event: ep,
                value: v,
            },
            s,
            label,
            Some(verdict),
            QueryKind::DebugHeld,
        );
    }

    fn on_viable_recv_verdict(
        &self,
        base: &ExecutionGraph,
        ep: EventId,
        src: EventId,
        s: EventId,
        label: &Label,
        verdict: bool,
    ) {
        self.inspect(
            base,
            PinnedChoice::Receive {
                event: ep,
                source: Some(src),
            },
            s,
            label,
            Some(verdict),
            QueryKind::Smaller,
        );
    }
}

fn run_case(name: &str, program: &VdProgram, priorities: &[usize]) -> Counts {
    let reference = Terminals::default();
    let config = Config::default()
        .collect_errors()
        .with_priorities(priorities.to_vec());
    explore(
        || program.clone(),
        &reference,
        config.clone().with_time_filter(),
    );
    let des = Terminals::default();
    explore(|| program.clone(), &des, config.clone().with_time_zombie());
    let audit = Audit {
        program,
        priorities,
        started: Instant::now(),
        state: Mutex::default(),
    };
    let observed = (audit, Terminals::default());
    explore(|| program.clone(), &observed, config.with_time_predicate());
    let wanted = reference.0.into_inner().unwrap();
    let actual = observed.1 .0.into_inner().unwrap();
    let duplicates = *observed.1 .1.lock().unwrap();
    let state = observed.0.state.into_inner().unwrap();
    eprintln!(
        "{name} priorities={priorities:?}: T1={} DES={} T2={} duplicates={} missing={} extra={}",
        wanted.len(),
        des.0.lock().unwrap().len(),
        actual.len(),
        duplicates,
        wanted.keys().filter(|k| !actual.contains_key(*k)).count(),
        actual.keys().filter(|k| !wanted.contains_key(*k)).count()
    );
    if duplicates > 0 {
        let mut by_target: BTreeMap<String, Vec<&Candidate>> = BTreeMap::new();
        for candidate in &state.admitted_hosts {
            by_target
                .entry(candidate.target.canonical_key())
                .or_default()
                .push(candidate);
        }
        for (key, hosts) in by_target.iter().filter(|(_, hosts)| hosts.len() > 1) {
            eprintln!("Repeated admitted target ({}) {key}", hosts.len());
            for host in hosts {
                eprintln!(
                    "r={} s={} host_time_feasible={}\n{}",
                    host.victim,
                    host.send,
                    must::check(&host.host).is_feasible(),
                    stamped(&host.host)
                );
            }
        }
    }
    assert_eq!(*reference.1.lock().unwrap(), 0);
    assert_eq!(*des.1.lock().unwrap(), 0);
    assert_eq!(
        wanted.keys().collect::<Vec<_>>(),
        des.0.lock().unwrap().keys().collect::<Vec<_>>(),
        "{name} DES priorities={priorities:?}"
    );
    assert_eq!(
        wanted.keys().collect::<Vec<_>>(),
        actual.keys().collect::<Vec<_>>(),
        "{name} T2 priorities={priorities:?}"
    );
    assert!(state.current.is_none());
    let mut counts = state.counts;
    for (r, s, owner, replacement) in &state.certified_owners {
        let actual_owner = state.admitted_hosts.iter().find(|c| {
            c.victim == *r
                && c.send == *s
                && same_stamped_graph(&c.host, owner)
                && same_stamped_graph(&c.target, replacement)
        });
        assert!(
            actual_owner.is_some(),
            "certified exact owner was never admitted by main search\n{}",
            stamped(owner)
        );
        counts.owner_certificates_with_actual_owner += 1;
    }
    for rejected in state.rejected.iter().filter(|c| c.smaller_true) {
        counts.rejected_by_smaller += 1;
        counts.rejected_structural_by_smaller += usize::from(rejected.structural);
        let key = rejected.target.canonical_key();
        let owned = state.admitted.contains(&key);
        counts.rejected_with_exact_owner += usize::from(owned);
        counts.rejected_with_visited_target += usize::from(state.visited.contains(&key));
        counts.rejected_with_terminal_extension +=
            usize::from(actual.values().any(|g| extends(g, &rejected.target)));
        counts.rejected_structural_without_owner += usize::from(rejected.structural && !owned);
        counts.witness_hosts_visited += rejected
            .witnesses
            .iter()
            .filter(|g| state.visited.contains(&g.canonical_key()))
            .count();
    }
    eprintln!(
        "{name} priorities={priorities:?} terminals={} {counts:?}",
        actual.len()
    );
    assert_eq!(duplicates, 0, "{name} duplicate terminal graphs");
    counts
}

fn send(dst: usize, value: &'static str, lo: u64, hi: u64) -> Op {
    Op::Send {
        dst,
        model: Model::Asyn,
        val: value,
        lo,
        hi,
    }
}

fn recv(sel: Sel) -> Op {
    Op::Recv {
        sel,
        blocking: true,
    }
}

#[test]
fn smaller_nondet_witness_has_a_reached_owner() {
    let program = VdProgram {
        threads: vec![
            vec![send(0, "a", 1, 5), recv(Sel::Any), Op::Nondet],
            vec![send(1, "g", 2, 2), recv(Sel::Eq("g")), send(0, "b", 1, 1)],
        ],
    };
    for priorities in [vec![0, 1], vec![1, 0]] {
        let counts = run_case("simple ND", &program, &priorities);
        assert!(counts.smaller_true > 0);
        assert!(counts.rejected_structural_by_smaller > 0);
        assert_eq!(counts.rejected_structural_without_owner, 0);
    }
}

#[test]
fn receive_and_nondet_choices_share_exact_targets() {
    let program = VdProgram {
        threads: vec![
            vec![send(0, "a", 1, 10), recv(Sel::Any), Op::Nondet],
            vec![
                send(1, "b", 2, 5),
                send(1, "c", 3, 6),
                recv(Sel::Any),
                Op::Nondet,
            ],
            vec![send(2, "x", 7, 7), recv(Sel::Eq("x")), send(0, "s", 1, 1)],
        ],
    };
    for priorities in [vec![0, 1, 2], vec![2, 1, 0], vec![1, 2, 0]] {
        let counts = run_case("RF plus ND", &program, &priorities);
        assert!(counts.receive_queries > 0);
        assert!(counts.smaller_true > 0);
        assert_eq!(counts.rejected_structural_without_owner, 0);
    }
}

#[test]
fn nested_revisit_distinguishes_doomed_partial_candidates() {
    for conditional in [false, true] {
        let future_send = if conditional {
            Op::SendIf {
                guard: 2,
                eq: "a",
                dst: 0,
                model: Model::Asyn,
                val: "y",
                lo: 1,
                hi: 1,
            }
        } else {
            send(0, "y", 1, 1)
        };
        let program = VdProgram {
            threads: vec![
                vec![send(0, "a", 1, 10), recv(Sel::Any)],
                vec![
                    send(1, "g", 2, 2),
                    recv(Sel::Eq("g")),
                    Op::Nondet,
                    future_send,
                ],
                vec![send(2, "x", 4, 4), recv(Sel::Eq("x")), send(0, "s", 1, 1)],
            ],
        };
        for priorities in [vec![0, 1, 2], vec![2, 1, 0], vec![1, 2, 0]] {
            run_case(
                if conditional {
                    "nested conditional"
                } else {
                    "nested unconditional"
                },
                &program,
                &priorities,
            );
        }
    }
}

#[test]
fn correlated_clock_two_receive_holders() {
    let program = VdProgram {
        threads: vec![
            vec![send(0, "d", 0, 100), send(0, "B", 20, 20), recv(Sel::Any)],
            vec![
                send(1, "w", 1, 20),
                recv(Sel::Eq("w")),
                send(0, "c", 1, 1),
                send(1, "m1", 1, 1),
                send(1, "m2", 1, 1),
                recv(Sel::Any),
            ],
            vec![send(2, "g", 9, 9), recv(Sel::Eq("g")), send(1, "s", 1, 1)],
        ],
    };
    run_case("correlated RF holders", &program, &[0, 1, 2]);
}

#[test]
fn correlated_clock_nondet_holders() {
    let program = VdProgram {
        threads: vec![
            vec![recv(Sel::Any)],
            vec![recv(Sel::Eq("q")), send(0, "x", 1, 1), send(2, "s", 1, 1)],
            vec![recv(Sel::Any), Op::Nondet],
            vec![send(1, "q", 1, 100), send(0, "w", 10, 10)],
            vec![
                send(4, "g", 5, 5),
                recv(Sel::Eq("g")),
                send(2, "early", 1, 1),
            ],
        ],
    };
    let counts = run_case("correlated ND holders", &program, &[0, 1, 2, 3, 4]);
    assert!(counts.owner_certificates > 0);
}

#[test]
fn positive_correlated_clock_two_receive_holders() {
    // Removing the initial d send leaves all delays strictly positive. u is selected
    // first, then v's c lower bound ties r's m lower bound; tid 0 wins the tie.
    let program = VdProgram {
        threads: vec![
            vec![send(0, "B", 20, 20), recv(Sel::Any)],
            vec![
                send(1, "w", 1, 20),
                recv(Sel::Eq("w")),
                send(0, "c", 1, 1),
                send(1, "m1", 1, 1),
                send(1, "m2", 1, 1),
                recv(Sel::Any),
            ],
            vec![send(2, "g", 9, 9), recv(Sel::Eq("g")), send(1, "s", 1, 1)],
        ],
    };
    for priorities in [vec![0, 1, 2], vec![2, 1, 0], vec![1, 2, 0]] {
        let counts = run_case("positive correlated RF holders", &program, &priorities);
        assert!(counts.owner_certificates > 0);
    }
}

#[test]
fn three_thread_correlated_clock_nondet_holders() {
    let program = VdProgram {
        threads: vec![
            vec![
                send(0, "q", 1, 100),
                send(0, "w", 10, 10),
                recv(Sel::Eq("q")),
                send(0, "x", 1, 1),
                send(1, "s", 1, 1),
                recv(Sel::Any),
            ],
            vec![recv(Sel::Any), Op::Nondet],
            vec![
                send(2, "g", 5, 5),
                recv(Sel::Eq("g")),
                send(1, "early", 1, 1),
            ],
        ],
    };
    for priorities in [vec![0, 1, 2], vec![2, 1, 0], vec![1, 2, 0]] {
        let counts = run_case("three-thread correlated ND holders", &program, &priorities);
        assert!(counts.owner_certificates > 0);
    }
}

#[derive(Clone)]
struct SummaryToggle {
    sequence: common::SeqProgram,
    summaries: bool,
}

impl Program for SummaryToggle {
    fn num_threads(&self) -> usize {
        self.sequence.num_threads()
    }
    fn next(&self, traces: &[Vec<Option<Val>>]) -> Vec<must::ThreadNext> {
        self.sequence.next(traces)
    }
    fn possible_future(&self, tid: usize, trace: &[Option<Val>]) -> Option<Vec<Label>> {
        self.summaries
            .then(|| self.sequence.possible_future(tid, trace).unwrap())
    }
}

struct RepairGateAudit<'a> {
    program: &'a SummaryToggle,
    pruned_hosts: Mutex<Vec<ExecutionGraph>>,
    repairing_revisits: Mutex<usize>,
}

impl Observer for RepairGateAudit<'_> {
    fn on_event_added(&self, g: &ExecutionGraph, e: EventId) {
        if e == EventId::new(1, 6)
            && g.reads_from(EventId::new(0, 1)) == Some(EventId::new(0, 0))
            && !g.contains(EventId::new(2, 1))
            && !must::time::gate_feasible(g, self.program, &[0, 1, 2])
        {
            // The extra send is harmless in the current graph. Its forced future is
            // infeasible, but that future contains the repairing send we must reach.
            assert!(must::check(g).is_feasible());
            assert!(
                !must::check(&must::time::forced_closure(g, self.program, &[0, 1, 2]))
                    .is_feasible()
            );
            self.pruned_hosts.lock().unwrap().push(g.clone());
        }
    }

    fn on_backward_revisit(
        &self,
        g: &ExecutionGraph,
        r: EventId,
        s: EventId,
        _deleted: &BTreeSet<EventId>,
    ) {
        if r == EventId::new(1, 5)
            && s == EventId::new(2, 2)
            && g.reads_from(EventId::new(0, 1)) == Some(EventId::new(0, 0))
        {
            *self.repairing_revisits.lock().unwrap() += 1;
        }
    }
}

fn gate_loss_target(sequence: &common::SeqProgram, fixed_w: bool) -> ExecutionGraph {
    let mut graph = ExecutionGraph::new();
    for (tid, labels) in sequence.threads.iter().enumerate() {
        for (idx, original) in labels.iter().enumerate() {
            let mut label = original.clone();
            if fixed_w && (tid, idx) == (1, 0) {
                let Label::Send { window, .. } = &mut label else {
                    unreachable!()
                };
                *window = must::Window::new(19, 19);
            }
            assert_eq!(graph.add_event(tid, label), EventId::new(tid, idx));
        }
    }
    for ((rt, ri), (st, si)) in [
        ((0, 1), (0, 0)),
        ((1, 1), (1, 0)),
        ((1, 5), (2, 2)),
        ((2, 1), (2, 0)),
    ] {
        graph.set_rf(EventId::new(rt, ri), Some(EventId::new(st, si)));
    }
    graph
}

/// Known, UNFIXED limitation: T1's five valid keys remain authoritative. This test
/// explicitly records T2's missing exact graph; passing does not endorse four as
/// the desired result. It must be updated when construction-safe gating fixes it.
#[test]
fn known_limitation_forward_gate_can_remove_the_repairing_send() {
    let s =
        |dst, value, lo, hi| Label::send_within(Model::Asyn, dst, value, must::Window::new(lo, hi));
    let sequence = common::SeqProgram::new(vec![
        vec![s(0, "B", 20, 20), Label::recv(must::Pred::any())],
        vec![
            s(1, "w", 1, 20),
            Label::recv(must::Pred::eq("w")),
            s(0, "c", 1, 1),
            s(1, "m1", 1, 1),
            s(1, "m2", 1, 1),
            Label::recv(must::Pred::any()),
            s(0, "extra", 1, 1),
        ],
        vec![
            s(2, "g", 9, 9),
            Label::recv(must::Pred::eq("g")),
            s(1, "s", 1, 1),
        ],
    ]);
    let program = SummaryToggle {
        sequence: sequence.clone(),
        summaries: true,
    };
    let expected = gate_loss_target(&sequence, false);
    assert!(must::consistent(&expected));
    assert_eq!(common::time_feasible_ref(&expected, &mut 20), Some(true));

    // Pin the only variable delivery to 19. The independent checker now considers
    // exactly one delay vector; this is a concrete feasible witness, not only SAT
    // from the production temporal solver.
    let fixed = gate_loss_target(&sequence, true);
    assert_eq!(common::time_feasible_ref(&fixed, &mut 1), Some(true));
    let must::time::TimedVerdict::Feasible(schedule) = must::check(&fixed) else {
        panic!("fixed schedule rejected")
    };
    for ((tid, idx), time) in [
        ((0, 0), 20),
        ((1, 0), 19),
        ((1, 2), 20),
        ((1, 3), 20),
        ((1, 4), 20),
        ((1, 6), 20),
        ((2, 0), 9),
        ((2, 2), 10),
    ] {
        assert_eq!(schedule.arr[&EventId::new(tid, idx)], time);
    }
    for ((tid, idx), time) in [((0, 1), 20), ((1, 1), 19), ((1, 5), 19), ((2, 1), 9)] {
        assert_eq!(schedule.fire[&EventId::new(tid, idx)], time);
    }

    let config = Config::default().collect_errors();
    let reference = Terminals::default();
    explore(
        || program.clone(),
        &reference,
        config.clone().with_time_filter(),
    );
    let wanted = reference.0.lock().unwrap().clone();
    assert_eq!(wanted.len(), 5, "authoritative T1 reference count");
    assert_eq!(*reference.1.lock().unwrap(), 0);
    let missing_key = format!("Full:{}", expected.canonical_key());
    assert!(wanted.contains_key(&missing_key));

    let des = Terminals::default();
    explore(|| program.clone(), &des, config.clone().with_time_zombie());
    assert_eq!(
        wanted.keys().collect::<Vec<_>>(),
        des.0.lock().unwrap().keys().collect::<Vec<_>>()
    );
    assert_eq!(*des.1.lock().unwrap(), 0);

    let gate = RepairGateAudit {
        program: &program,
        pruned_hosts: Mutex::default(),
        repairing_revisits: Mutex::default(),
    };
    let timed = (gate, Terminals::default());
    explore(
        || program.clone(),
        &timed,
        config.clone().with_time_predicate(),
    );
    let found = timed.1 .0.lock().unwrap();
    assert_eq!(found.len(), 4, "known unfixed loss; desired count is five");
    assert_eq!(*timed.1 .1.lock().unwrap(), 0);
    assert!(found.keys().all(|key| wanted.contains_key(key)));
    assert_eq!(
        wanted
            .keys()
            .filter(|key| !found.contains_key(*key))
            .collect::<Vec<_>>(),
        vec![&missing_key]
    );
    assert_eq!(timed.0.pruned_hosts.lock().unwrap().len(), 2);
    assert_eq!(*timed.0.repairing_revisits.lock().unwrap(), 0);

    let unknown = SummaryToggle {
        sequence,
        summaries: false,
    };
    let without_summaries = Terminals::default();
    explore(
        || unknown.clone(),
        &without_summaries,
        config.clone().with_time_predicate(),
    );
    assert_eq!(
        wanted.keys().collect::<Vec<_>>(),
        without_summaries
            .0
            .lock()
            .unwrap()
            .keys()
            .collect::<Vec<_>>()
    );
    assert_eq!(
        *without_summaries.1.lock().unwrap(),
        1,
        "known duplicate when summary gate falls back to raw feasibility"
    );

    let certified = (must::CountingObserver::new(), Terminals::default());
    explore(|| program.clone(), &certified, config.with_certified_time());
    assert_eq!(
        wanted.keys().collect::<Vec<_>>(),
        certified.1 .0.lock().unwrap().keys().collect::<Vec<_>>()
    );
    assert_eq!(*certified.1 .1.lock().unwrap(), 0);
    eprintln!("KNOWN LIMITATION: T1=5/5 DES=5/5 T2 exact-summary=4/4 (one missing), T2 unknown-summary=5/6 (one duplicate), certified=5/5; checks={} prunes={} unknown={}", certified.0.time_certificate_checks(), certified.0.time_certificate_prunes(), certified.0.time_certificate_unknown());
    eprintln!("MISSING EXACT KEY:\n{missing_key}\nConcrete schedule: w/u=19; B,c,m1,m2,extra=20; g=9; s=10; r consumes queued s at19; v consumes B at20.");
}
