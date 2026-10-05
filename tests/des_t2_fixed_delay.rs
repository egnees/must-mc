//! Checks the restricted chronological proof: blocking receives and strictly positive
//! point delays. These finite cases support, but do not replace, the proof argument.

mod common;

use std::collections::BTreeSet;

use common::{time_feasible_ref, SeqProgram};
use must::{explore, Config, CountingObserver, ExecutionCollector, Label, Model, Pred, Window};

fn keys(collector: &ExecutionCollector) -> BTreeSet<(u8, String)> {
    collector
        .full_keys()
        .into_iter()
        .map(|k| (0, k))
        .chain(
            collector
                .blocked()
                .into_iter()
                .map(|e| (1, e.canonical_key())),
        )
        .chain(collector.error_keys().into_iter().map(|k| (2, k)))
        .collect()
}

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        ((z ^ (z >> 31)) % n as u64) as usize
    }
}

#[test]
fn positive_point_delays_need_no_backward_revisits() {
    let mut random = Rng(0x4465_7350_696e_2026);
    let mut valid = 0;
    let mut references_filtered = 0;
    for case in 0..256 {
        let mut threads = Vec::new();
        for _ in 0..3 {
            let mut ops = Vec::new();
            for _ in 0..3 {
                let value = if random.below(2) == 0 { "a" } else { "b" };
                match random.below(10) {
                    0..=4 => {
                        let dst = random.below(3);
                        let model = if random.below(2) == 0 {
                            Model::Asyn
                        } else {
                            Model::P2p
                        };
                        let delay = 1 + random.below(4) as u64;
                        ops.push(Label::send_within(
                            model,
                            dst,
                            value,
                            Window::new(delay, delay),
                        ));
                    }
                    5..=8 => {
                        let pred = if random.below(2) == 0 {
                            Pred::any()
                        } else {
                            Pred::eq(value)
                        };
                        ops.push(Label::recv(pred));
                    }
                    _ => ops.push(Label::nondet(["a", "b"])),
                }
            }
            threads.push(ops);
        }
        let program = SeqProgram::new(threads);
        let reference = (CountingObserver::new(), ExecutionCollector::new());
        explore(
            || program.clone(),
            &reference,
            Config::default().collect_errors().with_time_filter(),
        );
        let wanted = keys(&reference.1);
        valid += wanted.len();
        references_filtered += reference.0.filtered();
        for priorities in [vec![0, 1, 2], vec![2, 1, 0]] {
            let observed = (CountingObserver::new(), ExecutionCollector::new());
            explore(
                || program.clone(),
                &observed,
                Config::default()
                    .collect_errors()
                    .with_time_predicate()
                    .with_priorities(priorities),
            );
            assert_eq!(keys(&observed.1), wanted, "case {case}");
            assert_eq!(
                observed.0.terminal() + observed.0.errors(),
                wanted.len(),
                "duplicates case {case}"
            );
            assert_eq!(
                observed.0.backward_revisits(),
                0,
                "admitted revisit case {case}"
            );
            assert_eq!(observed.0.filtered(), 0, "infeasible terminal case {case}");
            for execution in observed
                .1
                .full()
                .into_iter()
                .chain(observed.1.blocked())
                .chain(observed.1.errors())
            {
                let mut budget = 10_000;
                assert_eq!(
                    time_feasible_ref(execution.graph(), &mut budget),
                    Some(true),
                    "independent timing case {case}"
                );
            }
        }
    }
    assert!(valid > 256, "corpus must include branching");
    assert!(
        references_filtered > 0,
        "corpus must exercise timing rejection"
    );
    eprintln!("fixed positive delays: 256 programs, 512 T2 runs, {valid} reference valid keys, {references_filtered} filtered reference terminals, no admitted T2 revisits");
}
