mod common;

use common::SeqProgram;
use must::{explore, Config, ExecutionCollector, Label, Model, Pred, System, Window};

fn keys<P: must::Program>(factory: impl Fn() -> P + Sync, config: Config) -> Vec<String> {
    let collector = ExecutionCollector::new();
    explore(factory, &collector, config);
    let mut keys = collector.terminal_keys();
    keys.sort();
    assert!(keys.windows(2).all(|pair| pair[0] != pair[1]));
    keys
}

#[test]
fn send_first_preserves_asyn_selective_nonblocking_and_no_oota_graphs() {
    for program in [
        SeqProgram::new(vec![
            vec![
                Label::send(Model::Asyn, 1, "ignored"),
                Label::send(Model::Asyn, 1, "accepted"),
            ],
            vec![
                Label::recv_nb(Pred::eq("accepted")),
                Label::recv(Pred::eq("accepted")),
            ],
        ]),
        SeqProgram::new(vec![vec![
            Label::recv_nb(Pred::any()),
            Label::recv_nb(Pred::any()),
        ]]),
        SeqProgram::new(vec![
            vec![
                Label::recv(Pred::any()),
                Label::send(Model::Asyn, 1, "cycle"),
            ],
            vec![
                Label::recv(Pred::any()),
                Label::send(Model::Asyn, 0, "cycle"),
            ],
        ]),
    ] {
        let baseline = keys(|| program.clone(), Config::default());
        assert_eq!(
            keys(|| program.clone(), Config::default().with_send_first()),
            baseline
        );
        assert_eq!(
            keys(
                || program.clone(),
                Config::default().with_send_first().with_threads(3)
            ),
            baseline
        );
    }
}

fn branching() -> System {
    let mut system = System::new();
    system.add(|ctx| async move {
        ctx.send(2, "good", Model::Asyn);
    });
    system.add(|ctx| async move {
        ctx.send(2, "bad", Model::Asyn);
    });
    system.add(|ctx| async move {
        let value = ctx.recv_any().await;
        ctx.assert_that(value == "good", "value-dependent error");
        ctx.send(3, value, Model::Asyn);
    });
    system.add(|ctx| async move {
        ctx.recv_any().await;
    });
    system
}

#[test]
fn send_first_preserves_value_dependent_errors_and_parallel_graphs() {
    let baseline = keys(branching, Config::default().collect_errors());
    for threads in [1, 3] {
        assert_eq!(
            keys(
                branching,
                Config::default()
                    .collect_errors()
                    .with_send_first()
                    .with_threads(threads)
            ),
            baseline
        );
    }
}

#[test]
fn send_first_rejects_timed_regimes() {
    for config in [
        Config::default().collect_errors().with_time_filter(),
        Config::default().collect_errors().with_time_zombie(),
        Config::default().collect_errors().with_time_predicate(),
        Config::default().collect_errors().with_mailbox_time(),
    ] {
        assert!(std::panic::catch_unwind(|| keys(System::new, config.with_send_first())).is_err());
    }
}

#[test]
#[should_panic(expected = "send-first scheduling requires untimed labels")]
fn send_first_rejects_late_timed_labels() {
    let program = SeqProgram::new(vec![vec![
        Label::send(Model::Asyn, 1, "untimed"),
        Label::send_within(Model::Asyn, 1, "timed", Window::new(1, 2)),
    ]]);
    keys(|| program.clone(), Config::default().with_send_first());
}
