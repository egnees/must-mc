//! Trace annotations belong to the replayed execution, not to the explored event graph.
use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use must::{explore, Config, Ctx, ExecutionCollector, Model, Program, System, TraceLabel};

fn labels(labels: &[TraceLabel]) -> Vec<(usize, usize, String)> {
    labels
        .iter()
        .map(|label| {
            (
                label.tid,
                label.position,
                must::intern::resolve(label.value).to_string(),
            )
        })
        .collect()
}

fn annotated_sends() -> System {
    let mut system = System::new();
    system.add(|ctx: Ctx| async move {
        ctx.insert_label("before");
        ctx.send(0, "one", Model::Asyn);
        ctx.insert_label("between-a");
        ctx.insert_label("between-b");
        ctx.send(0, "two", Model::Asyn);
        ctx.insert_label("after");
    });
    system
}

#[test]
fn labels_stop_at_first_uncommitted_synchronous_event() {
    let system = annotated_sends();
    for (trace, expected) in [
        (vec![], vec![(0, 0, "before")]),
        (
            vec![None],
            vec![(0, 0, "before"), (0, 1, "between-a"), (0, 1, "between-b")],
        ),
        (
            vec![None, None],
            vec![
                (0, 0, "before"),
                (0, 1, "between-a"),
                (0, 1, "between-b"),
                (0, 2, "after"),
            ],
        ),
    ] {
        let actual = labels(&system.labels(&[trace]));
        assert_eq!(
            actual,
            expected
                .into_iter()
                .map(|(t, p, v)| (t, p, v.into()))
                .collect::<Vec<_>>()
        );
    }
    // A later replay must not contaminate an earlier prefix's annotations.
    assert_eq!(labels(&system.labels(&[vec![]])), [(0, 0, "before".into())]);
}

#[test]
fn blocked_receive_keeps_only_annotations_before_it() {
    let observer = ExecutionCollector::new();
    explore(
        || {
            let mut system = System::new();
            system.add(|ctx: Ctx| async move {
                ctx.insert_label("waiting");
                ctx.recv(|_| true).await;
                ctx.insert_label("received");
            });
            system
        },
        &observer,
        Config::default(),
    );
    assert_eq!(observer.blocked_count(), 1);
    assert_eq!(
        labels(observer.blocked()[0].labels()),
        [(0, 0, "waiting".into())]
    );
}

#[test]
fn completed_receive_records_final_label_and_renderer_shows_it() {
    let observer = ExecutionCollector::new();
    explore(
        || {
            let mut system = System::new();
            system.add(|ctx: Ctx| async move {
                ctx.send(0, "payload", Model::Asyn);
                ctx.insert_label("waiting-marker");
                let value = ctx.recv(|_| true).await;
                ctx.insert_label(format!("received-marker:{value}"));
            });
            system
        },
        &observer,
        Config::default(),
    );
    let executions = observer.full();
    assert_eq!(executions.len(), 1);
    assert_eq!(
        labels(executions[0].labels()),
        [
            (0, 1, "waiting-marker".into()),
            (0, 2, "received-marker:payload".into())
        ]
    );
    let rendered = must::render::render_execution(&executions[0]);
    let send = rendered.find("#0 ").expect("send keeps graph event index");
    let waiting = rendered.find("label[waiting-marker]").unwrap();
    let recv = rendered
        .find("#1 ")
        .expect("receive keeps graph event index");
    let received = rendered.find("label[received-marker:payload]").unwrap();
    let rf = rendered.find("rf:").unwrap();
    assert!(send < waiting && waiting < recv && recv < received && received < rf);
    assert!(rendered.contains("⟨0,1⟩←⟨0,0⟩"));
    assert!(!rendered.contains("local labels:"));
}

#[test]
fn errors_and_event_budget_do_not_leak_later_annotations() {
    for budget_error in [false, true] {
        let observer = ExecutionCollector::new();
        explore(
            || {
                let mut system = System::new().with_max_events(1);
                system.add(move |ctx: Ctx| async move {
                    ctx.insert_label("first");
                    if budget_error {
                        ctx.send(0, "one", Model::Asyn);
                        ctx.insert_label("before-limit");
                        ctx.send(0, "two", Model::Asyn);
                    } else {
                        ctx.assert_that(false, "failure");
                    }
                    ctx.insert_label("must-not-appear");
                });
                system
            },
            &observer,
            Config::default(),
        );
        let executions = observer.errors();
        assert_eq!(executions.len(), 1);
        let expected = if budget_error {
            vec![(0, 0, "first".into()), (0, 1, "before-limit".into())]
        } else {
            vec![(0, 0, "first".into())]
        };
        assert_eq!(labels(executions[0].labels()), expected);
    }
}

fn competing_sources(marked: bool) -> System {
    let mut system = System::new();
    system.add(move |ctx: Ctx| async move {
        let value = ctx.recv(|_| true).await;
        if marked {
            ctx.insert_label(format!("read:{value}"));
        }
    });
    system.add(|ctx: Ctx| async move {
        ctx.send(0, "a", Model::Asyn);
    });
    system.add(|ctx: Ctx| async move {
        ctx.send(0, "b", Model::Asyn);
    });
    system
}

#[test]
fn source_revisits_and_parallel_workers_keep_distinct_snapshots() {
    let reference = ExecutionCollector::new();
    explore(|| competing_sources(false), &reference, Config::default());
    let keys: BTreeSet<_> = reference.full_keys().into_iter().collect();
    assert_eq!(keys.len(), 2);
    for threads in [1, 4] {
        let observer = ExecutionCollector::new();
        explore(
            || competing_sources(true),
            &observer,
            Config::default().with_threads(threads),
        );
        assert_eq!(
            observer.full_keys().into_iter().collect::<BTreeSet<_>>(),
            keys
        );
        let mut seen = BTreeSet::new();
        for execution in observer.full() {
            let graph = execution.graph();
            let recv = graph.recvs()[0];
            let send = graph.reads_from(recv).unwrap();
            let expected = format!("read:{}", graph.label(send).val().unwrap());
            assert_eq!(labels(execution.labels()), [(0, 1, expected.clone())]);
            seen.insert(expected);
        }
        assert_eq!(seen, BTreeSet::from(["read:a".into(), "read:b".into()]));
    }
}

#[test]
fn many_labels_do_not_consume_budget_or_add_replays() {
    fn run(marker_count: usize) -> (usize, String) {
        let polls = Arc::new(AtomicUsize::new(0));
        let observer = ExecutionCollector::new();
        explore(
            || {
                let mut system = System::new().with_max_events(1);
                let polls = Arc::clone(&polls);
                system.add(move |ctx: Ctx| {
                    let polls = Arc::clone(&polls);
                    async move {
                        // Instrumentation only: the count never influences program behavior.
                        polls.fetch_add(1, Ordering::Relaxed);
                        for _ in 0..marker_count {
                            ctx.insert_label("marker");
                        }
                        ctx.send(0, "payload", Model::Asyn);
                        for _ in 0..marker_count {
                            ctx.insert_label("after");
                        }
                    }
                });
                system
            },
            &observer,
            Config::default(),
        );
        assert_eq!(observer.full_count(), 1);
        assert_eq!(observer.error_count(), 0);
        let execution = observer.full().remove(0);
        assert_eq!(execution.labels().len(), 2 * marker_count);
        (polls.load(Ordering::Relaxed), execution.canonical_key())
    }
    assert_eq!(run(0), run(200));
}

#[test]
fn filtered_executions_keep_annotations_without_changing_feasibility() {
    fn make(marked: bool) -> System {
        let mut system = System::new();
        system.add(move |ctx: Ctx| async move {
            let value = ctx.recv(|_| true).await;
            if marked {
                ctx.insert_label(format!("read:{value}"));
            }
        });
        system.add(|ctx: Ctx| async move {
            ctx.send_within(0, "slow", Model::Asyn, must::Window::new(50, 50));
        });
        system.add(|ctx: Ctx| async move {
            ctx.send_within(0, "fast", Model::Asyn, must::Window::new(1, 1));
        });
        system
    }
    let plain = ExecutionCollector::new();
    let marked = ExecutionCollector::new();
    let config = Config::default().collect_errors().with_time_filter();
    explore(|| make(false), &plain, config.clone());
    explore(|| make(true), &marked, config);
    assert_eq!(marked.full_count(), 1);
    assert_eq!(marked.filtered_count(), 1);
    assert_eq!(plain.full_keys(), marked.full_keys());
    assert_eq!(plain.filtered_keys(), marked.filtered_keys());
    assert_eq!(
        labels(marked.full()[0].labels()),
        [(0, 1, "read:fast".into())]
    );
    assert_eq!(
        labels(marked.filtered()[0].0.labels()),
        [(0, 1, "read:slow".into())]
    );
}

#[test]
fn renderer_interleaves_same_position_labels_and_keeps_marker_only_columns() {
    let observer = ExecutionCollector::new();
    explore(
        || {
            let mut system = annotated_sends();
            system.add(|ctx: Ctx| async move {
                ctx.insert_label("peer-first");
                ctx.insert_label("peer-second");
            });
            system
        },
        &observer,
        Config::default(),
    );
    let execution = observer.full().remove(0);
    assert_eq!(
        execution.graph().num_threads(),
        1,
        "thread 1 has no graph events"
    );
    let rendered = must::render::render_execution(&execution);
    let lines: Vec<_> = rendered.lines().collect();
    let second_column = lines[0]
        .find("T1")
        .expect("marker-only thread needs a column");
    assert_eq!(lines[1].find("label[peer-first]"), Some(second_column));
    let peer_second = lines[2].find("label[peer-second]").unwrap();
    // Event text contains a Unicode arrow; compare display columns, not byte offsets.
    assert_eq!(lines[2][..peer_second].chars().count(), second_column);
    for (row, token) in [
        "label[before]",
        "#0 ",
        "label[between-a]",
        "label[between-b]",
        "#1 ",
        "label[after]",
    ]
    .into_iter()
    .enumerate()
    {
        assert!(
            lines[row + 1].starts_with(token),
            "row {row}: {}",
            lines[row + 1]
        );
    }
    assert!(lines[7].starts_with("rf:"));
    assert!(!rendered.contains("local labels:"));
}
