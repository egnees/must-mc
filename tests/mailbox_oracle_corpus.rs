//! Checked-in RF graph corpus generated from the independent operational calendars.
//! Run `python3 tests/reference/generate_mailbox_corpus.py` to reproduce it.
use must::event::{EventId, Label, Model, Pred, Window};
use must::time::{check_mailbox, verify_mailbox_schedule, TimedVerdict};
use must::ExecutionGraph;

#[test]
fn production_builder_matches_independent_operational_corpus() {
    assert_eq!(
        check_corpus(include_str!("fixtures/mailbox_oracle.txt")),
        (2378, 1653)
    );
}

#[test]
fn mbox_builder_matches_independent_operational_corpus() {
    assert_eq!(
        check_corpus(include_str!("fixtures/mbox_oracle.txt")),
        (713, 401)
    );
}

fn check_corpus(corpus: &str) -> (usize, usize) {
    let mut tokens = corpus.split_whitespace();
    let count: usize = tokens.next().unwrap().parse().unwrap();
    let mut accepted = 0;
    for index in 0..count {
        let expected = tokens.next().unwrap() == "1";
        let threads: usize = tokens.next().unwrap().parse().unwrap();
        let mut g = ExecutionGraph::new();
        for t in 0..threads {
            let size: usize = tokens.next().unwrap().parse().unwrap();
            for _ in 0..size {
                let kind = tokens.next().unwrap();
                let lo: u64 = tokens.next().unwrap().parse().unwrap();
                let hi: u64 = tokens.next().unwrap().parse().unwrap();
                let label = if kind == "s" {
                    let model = match tokens.next().unwrap() {
                        "asyn" => Model::Asyn,
                        "p2p" => Model::P2p,
                        "mbox" => Model::Mbox,
                        _ => panic!(),
                    };
                    let dst = tokens.next().unwrap().parse().unwrap();
                    let value = tokens.next().unwrap();
                    Label::send_within(model, dst, value, Window::new(lo, hi))
                } else {
                    let pred = match tokens.next().unwrap() {
                        "*" => Pred::any(),
                        p => Pred::eq(p),
                    };
                    match kind {
                        "block" => Label::recv(pred),
                        "timeout" => Label::recv_timeout_timed(pred, Window::new(lo, hi)),
                        "poll" => Label::recv_poll_timed(pred, Window::new(lo, hi)),
                        _ => panic!(),
                    }
                };
                g.add_event(t, label);
            }
        }
        let recvs: Vec<_> = g.iter_recvs().collect();
        for r in recvs {
            let tid: isize = tokens.next().unwrap().parse().unwrap();
            let source = if tid < 0 {
                None
            } else {
                Some(EventId::new(
                    tid as usize,
                    tokens.next().unwrap().parse().unwrap(),
                ))
            };
            g.set_rf(r, source);
        }
        let verdict = check_mailbox(&g);
        assert_eq!(
            verdict.is_feasible(),
            expected,
            "corpus graph {index}: {g:?}, {verdict:?}"
        );
        // The feasibility-only entry point (the explorer's hot path) builds the same system
        // with the explanation tables switched off; it must never disagree.
        assert_eq!(
            must::time::eager_mailbox_feasible(&g),
            verdict.is_feasible(),
            "eager_mailbox_feasible disagrees with check_mailbox on corpus graph {index}"
        );
        if let TimedVerdict::Feasible(schedule) = verdict {
            accepted += 1;
            assert!(
                verify_mailbox_schedule(&g, &schedule),
                "invalid witness for corpus graph {index}"
            );
        }
    }
    assert_eq!(tokens.next(), None, "unconsumed corpus data");
    (count, accepted)
}
