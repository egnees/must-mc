use must_python::{Action, ErrorKind, Message, PythonModule, PythonOptions};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "must-python-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("solution.py"), source).unwrap();
        Self(path)
    }
    fn module(&self) -> PythonModule {
        self.options(PythonOptions::default())
    }
    fn options(&self, options: PythonOptions) -> PythonModule {
        PythonModule::new(self.0.join("solution.py"), "Solution", options).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn text(actions: &[Action]) -> String {
    match &actions[0] {
        Action::Local { message } => message.string_field("text").unwrap().unwrap(),
        _ => panic!("expected local action"),
    }
}

#[test]
fn prefixes_and_branch_isolation_without_pickle() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
module_values = []
class Solution(Process):
    def __init__(self):
        self.values = []
        self.unpickleable = lambda: None
    def get_state(self):
        raise RuntimeError('must not use get_state')
    def on_local_message(self, msg, ctx):
        module_values.append(msg['text'])
        self.values.append(msg['text'])
        ctx.send_local(Message('DELIVER', {'text': ','.join(module_values) + '/' + ','.join(self.values)}))
"#,
    );
    let module = fixture.module();
    let mut first = module.create("[]").unwrap();
    let mut second = first.clone();
    assert_eq!(
        text(
            &first
                .on_local_message(&Message::new("X", r#"{"text":"a"}"#), None)
                .unwrap()
        ),
        "a/a"
    );
    assert_eq!(
        text(
            &second
                .on_local_message(&Message::new("X", r#"{"text":"b"}"#), None)
                .unwrap()
        ),
        "b/b"
    );
    let prefix = first.clone();
    assert_eq!(
        text(
            &first
                .on_local_message(&Message::new("X", r#"{"text":"c"}"#), None)
                .unwrap()
        ),
        "a,c/a,c"
    );
    let mut replay = module.create("[]").unwrap();
    replay
        .on_local_message(&Message::new("X", r#"{"text":"a"}"#), None)
        .unwrap();
    assert_eq!(
        replay
            .on_local_message(&Message::new("X", r#"{"text":"c"}"#), None)
            .unwrap(),
        prefix
            .clone()
            .on_local_message(&Message::new("X", r#"{"text":"c"}"#), None)
            .unwrap()
    );
}

#[test]
fn dataclasses_prints_constructor_identity_and_fresh_arguments() {
    let fixture = Fixture::new(
        r#"
from dataclasses import dataclass
from anysystem import Process, Message
import os
print('import noise')
os.write(1, b'direct stdout noise')
@dataclass
class State:
    value: str
class Solution(Process):
    def __init__(self, name, processes):
        print('constructor noise')
        assert any(name is item for item in processes)
        assert len(processes) == 2
        processes.pop()
        self.state = State(name)
    def on_local_message(self, msg, ctx):
        ctx.send_local(Message('DELIVER', {'text': self.state.value}))
"#,
    );
    let module = fixture.module();
    let mut p = module
        .create(r#"["long-process-🚀", ["long-process-🚀", "other"]]"#)
        .unwrap();
    for _ in 0..3 {
        assert_eq!(
            text(&p.on_local_message(&Message::new("X", "{}"), None).unwrap()),
            "long-process-🚀"
        );
    }
}

#[test]
fn snapshots_unicode_sender_and_anysystem_action_grouping() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def __init__(self, name): self.name = name
    def on_message(self, msg, sender, ctx):
        ctx.set_timer('обычный', 2.5)
        ctx.send_local(Message('DELIVER', {'text': sender + msg['text']}))
        ctx.send(msg, self.name)
        msg['nested']['list'].append(3)
        ctx.send(msg, sender)
        ctx.set_timer_once('once', 1)
        ctx.cancel_timer('old')
"#,
    );
    let mut p = fixture.module().create(r#"["self🚀"]"#).unwrap();
    let a = p
        .on_message(
            &Message::new(
                "NET",
                r#"{"text":"\ud83d\ude80\n雪", "nested":{"list":[1,2]}}"#,
            ),
            "sender\"",
            None,
        )
        .unwrap();
    assert_eq!(a.len(), 6);
    match &a[0] {
        Action::Send { to, message } => {
            assert_eq!(to, "self🚀");
            assert!(message.data.contains("[1, 2]"));
            assert_eq!(message.string_field("text").unwrap().unwrap(), "🚀\n雪");
        }
        _ => panic!(),
    }
    match &a[1] {
        Action::Send { to, message } => {
            assert_eq!(to, "sender\"");
            assert!(message.data.contains("[1, 2, 3]"));
        }
        _ => panic!(),
    }
    assert_eq!(text(&a[2..]), "sender\"🚀\n雪");
    assert_eq!(
        a[3],
        Action::SetTimer {
            name: "обычный".into(),
            delay: 2.5,
            once: false
        }
    );
    assert_eq!(
        a[4],
        Action::SetTimer {
            name: "once".into(),
            delay: 1.,
            once: true
        }
    );
    assert_eq!(a[5], Action::CancelTimer { name: "old".into() });
}

#[test]
fn timers_clock_optional_start_and_error_rollback() {
    let fixture = Fixture::new(
        r#"
from anysystem import Message
class Solution:
    def on_timer(self, name, ctx):
        ctx.send_local(Message('DELIVER', {'text': name + ':' + str(ctx.time())}))
    def on_message(self, msg, sender, ctx):
        raise ValueError('broken callback')
"#,
    );
    let mut p = fixture.module().create("[]").unwrap();
    assert!(p.on_start(None).unwrap().is_empty());
    assert_eq!(
        p.on_timer("tick", None).unwrap_err().kind(),
        ErrorKind::Unsupported
    );
    assert_eq!(text(&p.on_timer("tick", Some(12.5)).unwrap()), "tick:12.5");
    let error = p
        .on_message(&Message::new("X", "{}"), "s", None)
        .unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Execution);
    assert!(error.to_string().contains("solution.py"));
    assert!(error.to_string().contains("in on_message"));
    assert!(error.to_string().contains("broken callback"));
    assert_eq!(text(&p.on_timer("tick", Some(13.5)).unwrap()), "tick:13.5");
    assert!(p.on_timer("tick", Some(f64::NAN)).is_err());
}

#[test]
fn seeded_random_uuid_and_message_identity_hash_are_replayable() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
import random, uuid
class Solution(Process):
    def __init__(self):
        self.rng = random.Random()
        self.initial = str(uuid.uuid4())
        self.messages = {Message('A', {}), Message('B', {})}
    def on_local_message(self, msg, ctx):
        value = [self.initial, random.random(), self.rng.random(), str(uuid.uuid4()), [hash(m) for m in self.messages]]
        ctx.send_local(Message('DELIVER', {'text': str(value)}))
"#,
    );
    let run = |module: PythonModule| {
        let mut p = module.create("[]").unwrap();
        (0..4)
            .map(|_| p.on_local_message(&Message::new("X", "{}"), None).unwrap())
            .collect::<Vec<_>>()
    };
    let first = run(fixture.module());
    assert_eq!(first, run(fixture.module()));
    assert_ne!(
        first,
        run(fixture.options(PythonOptions {
            seed: 44,
            ..Default::default()
        }))
    );
}

#[test]
fn helper_modules_are_isolated_between_branches() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
import helper
class Solution(Process):
    def on_local_message(self, msg, ctx):
        helper.values.append(msg['text'])
        ctx.send_local(Message('DELIVER', {'text': ','.join(helper.values)}))
"#,
    );
    std::fs::write(fixture.0.join("helper.py"), "values = []\n").unwrap();
    let module = fixture.module();
    let mut a = module.create("[]").unwrap();
    let mut b = a.clone();
    assert_eq!(
        text(
            &a.on_local_message(&Message::new("X", r#"{"text":"a"}"#), None)
                .unwrap()
        ),
        "a"
    );
    assert_eq!(
        text(
            &b.on_local_message(&Message::new("X", r#"{"text":"b"}"#), None)
                .unwrap()
        ),
        "b"
    );
    assert_eq!(
        text(
            &a.on_local_message(&Message::new("X", r#"{"text":"c"}"#), None)
                .unwrap()
        ),
        "a,c"
    );
}

#[test]
fn cached_prefixes_work_at_capacity_and_across_threads() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def on_local_message(self, msg, ctx): ctx.send_local(msg)
"#,
    );
    let module = fixture.options(PythonOptions {
        max_states: 2,
        workers: 4,
        ..Default::default()
    });
    let mut p = module.create("[]").unwrap();
    let expected = p
        .on_local_message(&Message::new("DELIVER", r#"{"text":"ok"}"#), None)
        .unwrap();
    assert_eq!(p.on_start(None).unwrap_err().kind(), ErrorKind::Resource);
    std::thread::scope(|scope| {
        for _ in 0..8 {
            let expected = &expected;
            let module = &module;
            scope.spawn(move || {
                for _ in 0..50 {
                    let mut p = module.create("[]").unwrap();
                    assert_eq!(
                        &p.on_local_message(&Message::new("DELIVER", r#"{"text":"ok"}"#), None)
                            .unwrap(),
                        expected
                    );
                }
            });
        }
    });
}

#[test]
fn callback_hang_is_bounded_and_worker_is_stopped() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def on_start(self, ctx):
        while True: pass
"#,
    );
    let mut p = fixture
        .options(PythonOptions {
            timeout: Duration::from_millis(500),
            ..Default::default()
        })
        .create("[]")
        .unwrap();
    let before = Instant::now();
    assert_eq!(p.on_start(None).unwrap_err().kind(), ErrorKind::Resource);
    assert!(before.elapsed() < Duration::from_secs(4));
    assert_eq!(p.on_start(None).unwrap_err().kind(), ErrorKind::Transport);
}

#[test]
fn import_hang_is_bounded() {
    let fixture = Fixture::new("while True: pass\n");
    let before = Instant::now();
    let error = PythonModule::new(
        fixture.0.join("solution.py"),
        "Solution",
        PythonOptions {
            timeout: Duration::from_millis(500),
            ..Default::default()
        },
    )
    .err()
    .unwrap();
    assert_eq!(error.kind(), ErrorKind::Resource);
    assert!(before.elapsed() < Duration::from_secs(4));
}

#[test]
fn nondeterministic_prefix_is_rejected() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
from pathlib import Path
class Solution(Process):
    def on_start(self, ctx):
        path = Path(__file__).with_name('counter')
        number = int(path.read_text()) + 1 if path.exists() else 0
        path.write_text(str(number))
        ctx.send_local(Message('DELIVER', {'text': str(number)}))
"#,
    );
    let mut p = fixture.module().create("[]").unwrap();
    p.on_start(None).unwrap();
    let error = p.on_start(None).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Execution);
    assert!(error.to_string().contains("nondeterministic"));
}

#[test]
fn invalid_input_missing_class_and_action_flood_are_errors() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def on_start(self, ctx):
        for _ in range(10001): ctx.send_local(Message('X', {}))
"#,
    );
    assert!(PythonModule::new(
        fixture.0.join("solution.py"),
        "Missing",
        PythonOptions::default()
    )
    .is_err());
    let module = fixture.module();
    assert!(module.create("{}").is_err());
    let mut p = module.create("[]").unwrap();
    assert_eq!(p.on_start(None).unwrap_err().kind(), ErrorKind::Resource);
    assert_eq!(
        p.on_message(&Message::new("X", "NaN"), "sender", None)
            .unwrap_err()
            .kind(),
        ErrorKind::Execution
    );
    assert_eq!(
        Message::new("X", r#"{"other":1}"#)
            .string_field("text")
            .unwrap(),
        None
    );
    assert!(Message::new("X", r#"{"text":1}"#)
        .string_field("text")
        .is_err());
}

#[test]
fn process_identity_separates_random_streams() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
import uuid
class Solution(Process):
    def __init__(self, name, processes):
        self.value = str(uuid.uuid4())
    def on_start(self, ctx):
        ctx.send_local(Message('DELIVER', {'text': self.value}))
"#,
    );
    let module = fixture.module();
    let a = text(
        &module
            .create(r#"["0",["0","1"]]"#)
            .unwrap()
            .on_start(None)
            .unwrap(),
    );
    let b = text(
        &module
            .create(r#"["1",["0","1"]]"#)
            .unwrap()
            .on_start(None)
            .unwrap(),
    );
    assert_ne!(a, b);
    let another = fixture.module();
    assert_eq!(
        a,
        text(
            &another
                .create(r#"["0", ["0", "1"]]"#)
                .unwrap()
                .on_start(None)
                .unwrap()
        )
    );
    assert_eq!(
        b,
        text(
            &another
                .create(r#"["1", ["0", "1"]]"#)
                .unwrap()
                .on_start(None)
                .unwrap()
        )
    );
}

#[test]
fn swallowed_missing_clock_is_still_unsupported() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def on_start(self, ctx):
        try:
            ctx.time()
        except Exception:
            pass
        ctx.send_local(Message('DELIVER', {'text': 'apparently fine'}))
"#,
    );
    let mut p = fixture.module().create("[]").unwrap();
    assert_eq!(p.on_start(None).unwrap_err().kind(), ErrorKind::Unsupported);
    assert_eq!(text(&p.on_start(Some(1.)).unwrap()), "apparently fine");
}

#[test]
fn swallowed_action_limit_is_still_resource_error() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def on_local_message(self, msg, ctx):
        try:
            if msg['case'] == 'bytes':
                ctx.send(Message('X', {'data': 'x' * (8 * 1024 * 1024)}), 'peer')
            else:
                for _ in range(10001):
                    ctx.send_local(Message('X', {}))
        except MemoryError:
            pass
"#,
    );
    let mut p = fixture.module().create("[]").unwrap();
    for case in ["bytes", "count"] {
        let message = Message::new("TEST", format!(r#"{{"case":"{case}"}}"#));
        assert_eq!(
            p.on_local_message(&message, None).unwrap_err().kind(),
            ErrorKind::Resource
        );
    }
}

#[test]
fn racing_identical_misses_share_constructor_transition_and_state_limit() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def on_local_message(self, msg, ctx): ctx.send_local(msg)
"#,
    );
    let module = fixture.options(PythonOptions {
        max_states: 2,
        workers: 12,
        ..Default::default()
    });
    let barrier = std::sync::Barrier::new(12);
    std::thread::scope(|scope| {
        for _ in 0..12 {
            let module = &module;
            let barrier = &barrier;
            scope.spawn(move || {
                barrier.wait();
                let mut p = module.create("[]").unwrap();
                let actions = p
                    .on_local_message(&Message::new("DELIVER", r#"{"text":"same"}"#), None)
                    .unwrap();
                assert_eq!(text(&actions), "same");
                assert_eq!(p.on_start(None).unwrap_err().kind(), ErrorKind::Resource);
            });
        }
    });
}

#[test]
fn cache_hits_and_other_worker_misses_continue_while_python_miss_is_running() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
from pathlib import Path
import time
class Solution(Process):
    def on_local_message(self, msg, ctx):
        if msg['text'] == 'slow':
            Path(__file__).with_name('started').touch()
            while not Path(__file__).with_name('finish').exists():
                time.sleep(0.005)
        ctx.send_local(msg)
"#,
    );
    let module = fixture.options(PythonOptions {
        workers: 2,
        ..Default::default()
    });
    module
        .create("[]")
        .unwrap()
        .on_local_message(&Message::new("DELIVER", r#"{"text":"cached"}"#), None)
        .unwrap();
    std::thread::scope(|scope| {
        let slow = scope.spawn(|| {
            module
                .create("[]")
                .unwrap()
                .on_local_message(&Message::new("DELIVER", r#"{"text":"slow"}"#), None)
        });
        let deadline = Instant::now() + Duration::from_secs(4);
        while !fixture.0.join("started").exists() {
            assert!(Instant::now() < deadline, "Python callback did not start");
            std::thread::sleep(Duration::from_millis(5));
        }
        let actions = module
            .create("[]")
            .unwrap()
            .on_local_message(&Message::new("DELIVER", r#"{"text":"cached"}"#), None)
            .unwrap();
        let uncached = module
            .create("[]")
            .unwrap()
            .on_local_message(&Message::new("DELIVER", r#"{"text":"uncached"}"#), None);
        std::fs::write(fixture.0.join("finish"), "").unwrap();
        assert_eq!(text(&actions), "cached");
        assert_eq!(text(&uncached.unwrap()), "uncached");
        assert_eq!(text(&slow.join().unwrap().unwrap()), "slow");
    });
}

#[test]
fn shared_callbacks_reuse_actions_and_preserve_typed_keys() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def on_local_message(self, msg, ctx):
        ctx.send_local(Message('DELIVER', {'text': msg['text']}))
    def on_message(self, msg, sender, ctx):
        ctx.send_local(Message('DELIVER', {'text': sender + msg['text']}))
"#,
    );
    let module = fixture.module();
    let initial = module.create("[]").unwrap();
    let message = Message::new("SEND", r#"{"text":"quoted\\\""}"#);
    let first = initial
        .clone()
        .on_local_message_shared(&message, None)
        .unwrap();
    let second = initial
        .clone()
        .on_local_message_shared(&message, None)
        .unwrap();
    assert!(std::sync::Arc::ptr_eq(&first, &second));
    let local = initial.clone().on_local_message(&message, None).unwrap();
    assert_eq!(first.as_ref(), local);
    let network = initial
        .clone()
        .on_message_shared(&message, "0", None)
        .unwrap();
    assert_ne!(first.as_ref(), network.as_ref());
    assert!(initial
        .clone()
        .on_message_shared(&message, "0", Some(f64::NAN))
        .is_err());
}

#[test]
#[ignore = "cached Python callback throughput benchmark"]
fn cached_callback_throughput() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def on_local_message(self, msg, ctx):
        ctx.send_local(Message('DELIVER', {'text': 'x' * 16384 + msg['text']}))
"#,
    );
    let module = fixture.module();
    let process = module.create("[]").unwrap();
    let message = Message::new("SEND", r#"{"text":"payload"}"#);
    let expected = process
        .clone()
        .on_local_message_shared(&message, None)
        .unwrap();
    const CALLS: usize = 200_000;
    let start = Instant::now();
    for _ in 0..CALLS {
        std::hint::black_box(process.clone().on_local_message(&message, None).unwrap());
    }
    let owned = start.elapsed();
    let start = Instant::now();
    for _ in 0..CALLS {
        std::hint::black_box(
            process
                .clone()
                .on_local_message_shared(&message, None)
                .unwrap(),
        );
    }
    let shared = start.elapsed();
    assert!(std::sync::Arc::ptr_eq(
        &expected,
        &process
            .clone()
            .on_local_message_shared(&message, None)
            .unwrap()
    ));
    eprintln!("cached callbacks={CALLS}, action payload=16 KiB, owned={owned:?}, shared={shared:?}, ratio={:.2}", owned.as_secs_f64() / shared.as_secs_f64());
}

#[test]
fn histories_migrate_between_interpreters_with_identical_random_and_global_state() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
import helper, random, uuid
class Solution(Process):
    def __init__(self):
        self.rng = random.Random()
        self.values = []
        self.messages = {Message('A', {}), Message('B', {})}
    def on_local_message(self, msg, ctx):
        helper.values.append(msg['text'])
        self.values.append(msg['text'])
        value = [self.values, helper.values, random.random(), self.rng.random(), str(uuid.uuid4()), [hash(m) for m in self.messages]]
        ctx.send_local(Message('DELIVER', {'text': str(value)}))
"#,
    );
    std::fs::write(fixture.0.join("helper.py"), "values = []\n").unwrap();
    let single = fixture.module();
    let pool = fixture.options(PythonOptions {
        workers: 4,
        ..Default::default()
    });
    let message = |value: &str| Message::new("X", format!(r#"{{"text":"{value}"}}"#));
    let mut expected = single.create("[]").unwrap();
    let mut prefix = pool.create("[]").unwrap();
    for value in ["first", "second", "third"] {
        assert_eq!(
            prefix.on_local_message(&message(value), None).unwrap(),
            expected.on_local_message(&message(value), None).unwrap()
        );
    }
    let barrier = std::sync::Barrier::new(8);
    let branches = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..8)
            .map(|i| {
                let mut branch = prefix.clone();
                let barrier = &barrier;
                let message = &message;
                scope.spawn(move || {
                    barrier.wait();
                    let actions = branch
                        .on_local_message(&message(&i.to_string()), None)
                        .unwrap();
                    (branch, actions)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });
    for (i, (mut branch, actions)) in branches.into_iter().enumerate() {
        let mut reference = expected.clone();
        assert_eq!(
            actions,
            reference
                .on_local_message(&message(&i.to_string()), None)
                .unwrap()
        );
        assert_eq!(
            branch
                .on_local_message(&message("back-to-main"), None)
                .unwrap(),
            reference
                .on_local_message(&message("back-to-main"), None)
                .unwrap()
        );
    }
}

#[test]
fn distinct_racing_misses_respect_the_shared_state_limit() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def on_local_message(self, msg, ctx): ctx.send_local(msg)
"#,
    );
    let module = fixture.options(PythonOptions {
        workers: 4,
        max_states: 2,
        ..Default::default()
    });
    let prefix = module.create("[]").unwrap();
    let barrier = std::sync::Barrier::new(8);
    let results = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..8)
            .map(|i| {
                let mut process = prefix.clone();
                let barrier = &barrier;
                scope.spawn(move || {
                    barrier.wait();
                    process
                        .on_local_message(&Message::new("X", format!(r#"{{"text":"{i}"}}"#)), None)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });
    assert_eq!(results.iter().filter(|r| r.is_ok()).count(), 1);
    for error in results.into_iter().filter_map(Result::err) {
        assert_eq!(error.kind(), ErrorKind::Resource);
    }
}

#[test]
fn large_history_migration_falls_back_without_limiting_valid_callbacks() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def __init__(self): self.lengths = []
    def on_local_message(self, msg, ctx):
        self.lengths.append(len(msg['text']))
        ctx.send_local(Message('DELIVER', {'text': str(self.lengths)}))
"#,
    );
    let module = fixture.options(PythonOptions {
        workers: 2,
        ..Default::default()
    });
    let mut process = module.create("[]").unwrap();
    let large = Message::new(
        "X",
        format!(r#"{{"text":"{}"}}"#, "x".repeat(3 * 1024 * 1024)),
    );
    for _ in 0..3 {
        process.on_local_message(&large, None).unwrap();
    }
    let actions = std::thread::spawn(move || {
        process.on_local_message(&Message::new("X", r#"{"text":"last"}"#), None)
    })
    .join()
    .unwrap()
    .unwrap();
    assert_eq!(text(&actions), "[3145728, 3145728, 3145728, 4]");
}

#[test]
fn pooled_workers_preserve_the_existing_response_frame_capacity() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
class Solution(Process):
    def on_local_message(self, msg, ctx):
        ctx.send_local(Message('DELIVER', {'text': 'x' * (5 * 1024 * 1024)}))
"#,
    );
    let module = fixture.options(PythonOptions {
        workers: 2,
        ..Default::default()
    });
    let mut process = module.create("[]").unwrap();
    let actions = process
        .on_local_message(&Message::new("X", "{}"), None)
        .unwrap();
    assert_eq!(text(&actions).len(), 5 * 1024 * 1024);
}

#[test]
fn imported_history_divergence_is_rejected_and_can_be_retried() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
import helper
class Solution(Process):
    def on_local_message(self, msg, ctx):
        ctx.send_local(Message('DELIVER', {'text': str(helper.value)}))
"#,
    );
    let helper = fixture.0.join("helper.py");
    std::fs::write(&helper, "value = 1\n").unwrap();
    let module = fixture.options(PythonOptions {
        workers: 2,
        ..Default::default()
    });
    let mut process = module.create("[]").unwrap();
    process
        .on_local_message(&Message::new("X", r#"{"step":1}"#), None)
        .unwrap();
    std::fs::write(&helper, "value = 2\n").unwrap();
    std::thread::spawn(move || {
        let message = Message::new("X", r#"{"step":2}"#);
        let error = process.on_local_message(&message, None).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Execution);
        assert!(error
            .to_string()
            .contains("imported callback outputs changed"));
        std::fs::write(&helper, "value = 1\n").unwrap();
        assert_eq!(
            text(&process.on_local_message(&message, None).unwrap()),
            "1"
        );
    })
    .join()
    .unwrap();
}

#[test]
fn receive_predicates_snapshot_branches_persist_and_reset() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def __init__(self):
        self.value = 0
    def on_local_message(self, msg, ctx):
        self.value = msg['value']
        if msg.type == 'SET':
            ctx.set_predicate(lambda message: message['value'] == self.value)
        elif msg.type == 'RESET':
            ctx.set_predicate(None)
"#,
    );
    for workers in [1, 12] {
        let module = fixture.options(PythonOptions {
            workers,
            ..PythonOptions::default()
        });
        let mut process = module.create("[]").unwrap();
        assert!(process.receive_predicate().unwrap().is_none());
        process
            .on_local_message(&Message::new("SET", r#"{"value":1}"#), None)
            .unwrap();
        let first = process.receive_predicate().unwrap().unwrap();
        let mut branch = process.clone();
        process
            .on_local_message(&Message::new("UPDATE", r#"{"value":2}"#), None)
            .unwrap();
        branch
            .on_local_message(&Message::new("UPDATE", r#"{"value":3}"#), None)
            .unwrap();
        let second = process.receive_predicate().unwrap().unwrap();
        let third = branch.receive_predicate().unwrap().unwrap();
        std::thread::scope(|scope| {
            for (predicate, expected) in [(first, 1), (second, 2), (third, 3)] {
                scope.spawn(move || {
                    for value in 1..=3 {
                        let message = Message::new("DATA", format!("{{\"value\":{value}}}"));
                        assert_eq!(predicate.matches(&message).unwrap(), value == expected);
                        assert_eq!(predicate.matches(&message).unwrap(), value == expected);
                    }
                });
            }
        });
        process
            .on_local_message(&Message::new("RESET", r#"{"value":4}"#), None)
            .unwrap();
        assert!(process.receive_predicate().unwrap().is_none());
    }
}

#[test]
fn receive_predicate_errors_and_queries_do_not_advance_history() {
    for expression in ["True", "1", "1 / 0"] {
        let fixture = Fixture::new(&format!("from anysystem import Process\nclass Solution(Process):\n    def on_start(self, ctx):\n        ctx.set_predicate(lambda msg: {expression})\n"));
        let module = fixture.options(PythonOptions {
            max_states: 2,
            ..PythonOptions::default()
        });
        let mut process = module.create("[]").unwrap();
        assert!(process.on_start(None).unwrap().is_empty());
        let predicate = process.receive_predicate().unwrap().unwrap();
        // Repeating the exact queries verifies failures never become cached
        // successful answers in either the shared or thread-local cache.
        for value in [0, 1, 2, 0, 1, 2] {
            let result = predicate.matches(&Message::new("DATA", format!("{{\"value\":{value}}}")));
            if expression == "True" {
                assert!(result.unwrap());
            } else {
                assert_eq!(result.unwrap_err().kind(), ErrorKind::Execution);
            }
        }
    }
}

#[test]
fn borrowed_predicate_queries_share_results_across_snapshots_and_threads() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def on_start(self, ctx):
        ctx.set_predicate(lambda msg: msg.type == 'DATA' and msg['value'] == 7)
"#,
    );
    let module = fixture.options(PythonOptions {
        workers: 12,
        ..PythonOptions::default()
    });
    let mut process = module.create("[]").unwrap();
    process.on_start(None).unwrap();
    std::thread::scope(|scope| {
        for _ in 0..12 {
            let predicate = process.receive_predicate().unwrap().unwrap();
            scope.spawn(move || {
                for _ in 0..20 {
                    assert!(predicate.matches_parts("DATA", r#"{"value":7}"#).unwrap());
                    assert!(!predicate.matches_parts("ACK", r#"{"value":7}"#).unwrap());
                    assert!(!predicate.matches_parts("DATA", r#"{"value":8}"#).unwrap());
                }
            });
        }
    });
    let predicate = process.receive_predicate().unwrap().unwrap();
    assert_eq!(
        predicate
            .matches_parts("DATA", "not json")
            .unwrap_err()
            .kind(),
        ErrorKind::Execution
    );
    assert!(predicate.matches_parts("DATA", r#"{"value":7}"#).unwrap());
}

#[test]
fn sender_predicate_cache_distinguishes_transport_source() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def on_start(self, ctx):
        ctx.set_sender_predicate(lambda msg, sender: sender == '1' and msg.type == 'DATA')
"#,
    );
    let module = fixture.module();
    let mut process = module.create("[]").unwrap();
    process.on_start(None).unwrap();
    let predicate = process.receive_predicate().unwrap().unwrap();
    for _ in 0..3 {
        assert!(predicate.matches_parts_from("DATA", "{}", "1").unwrap());
        assert!(!predicate.matches_parts_from("DATA", "{}", "2").unwrap());
        assert!(!predicate.matches_parts_from("ACK", "{}", "1").unwrap());
    }
    assert_eq!(
        predicate.matches_parts("DATA", "{}").unwrap_err().kind(),
        ErrorKind::Execution
    );
}

#[test]
fn sender_predicate_typeerror_is_not_retried_as_message_only() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def on_start(self, ctx):
        def broken(msg, sender):
            raise TypeError('sender predicate broke')
        ctx.set_sender_predicate(broken)
"#,
    );
    let module = fixture.module();
    let mut process = module.create("[]").unwrap();
    process.on_start(None).unwrap();
    let error = process
        .receive_predicate()
        .unwrap()
        .unwrap()
        .matches_parts_from("DATA", "{}", "1")
        .unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Execution);
    assert!(error.to_string().contains("sender predicate broke"));
}

#[test]
fn audited_state_cycles_repeat_actions_and_keep_short_representatives() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.bit = False
    def on_local_message(self, msg, ctx):
        self.bit = not self.bit
        ctx.send_local(Message('DELIVER', {'text': str(self.bit)}))
"#,
    );
    let module = fixture.options(PythonOptions {
        max_states: 2,
        ..PythonOptions::default()
    });
    let mut process = module.create("[]").unwrap();
    for turn in 0..100 {
        assert_eq!(
            text(
                &process
                    .on_local_message(&Message::new("X", "{}"), None)
                    .unwrap()
            ),
            if turn % 2 == 0 { "True" } else { "False" }
        );
    }
    let stats = module.cache_stats().unwrap();
    assert_eq!(stats.states, 2);
    assert_eq!(stats.transition_misses, 2);
    assert_eq!(stats.semantic_merges, 1);
    assert_eq!(stats.transition_hits, 98);
    // A new input misses after the cycle and must replay the constructor, not
    // follow a cyclic import history or suppress another emitted action.
    assert_eq!(
        text(
            &process
                .on_local_message(&Message::new("Y", "{}"), None)
                .unwrap()
        ),
        "True"
    );
}

#[test]
fn audited_state_merges_commuting_receives_with_bound_sender_predicate() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
from collections import defaultdict
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.seen = defaultdict(set)
    def accept(self, msg, sender):
        return sender not in self.seen.get(msg['text'], ())
    def on_message(self, msg, sender, ctx):
        self.seen[msg['text']].add(sender)
        ctx.set_sender_predicate(self.accept)
    def on_local_message(self, msg, ctx):
        ctx.send_local(Message('DELIVER', {'text': str(len(self.seen['x']))}))
"#,
    );
    let module = fixture.module();
    let root = module.create("[]").unwrap();
    let mut ab = root.clone();
    let mut ba = root;
    let msg = Message::new("X", r#"{"text":"x"}"#);
    ab.on_message(&msg, "a", None).unwrap();
    ab.on_message(&msg, "b", None).unwrap();
    ba.on_message(&msg, "b", None).unwrap();
    ba.on_message(&msg, "a", None).unwrap();
    assert!(module.cache_stats().unwrap().semantic_merges >= 1);
    for p in [&mut ab, &mut ba] {
        assert!(p
            .receive_predicate()
            .unwrap()
            .unwrap()
            .matches_parts_from("X", r#"{"text":"fresh"}"#, "a")
            .unwrap());
        assert!(!p
            .receive_predicate()
            .unwrap()
            .unwrap()
            .matches_parts_from(&msg.kind, &msg.data, "a")
            .unwrap());
        assert!(p
            .receive_predicate()
            .unwrap()
            .unwrap()
            .matches_parts_from(&msg.kind, &msg.data, "c")
            .unwrap());
        assert_eq!(text(&p.on_local_message(&msg, None).unwrap()), "2");
    }
}

#[test]
fn audited_functions_with_private_globals_fall_back_without_merging_outputs() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.fn = None
    def on_local_message(self, msg, ctx):
        if msg.type == 'SET':
            namespace = {'__name__': '_must_solution', 'value': msg['value']}
            exec('def answer(): return value', namespace)
            self.fn = namespace['answer']
        else:
            ctx.send_local(Message('DELIVER', {'text': self.fn()}))
"#,
    );
    for semantic_state_cache in [false, true] {
        let module = fixture.options(PythonOptions {
            semantic_state_cache,
            workers: 2,
            ..Default::default()
        });
        let root = module.create("[]").unwrap();
        let mut one = root.clone();
        let mut two = root;
        one.on_local_message(&Message::new("SET", r#"{"value":"one"}"#), None)
            .unwrap();
        two.on_local_message(&Message::new("SET", r#"{"value":"two"}"#), None)
            .unwrap();
        let query = Message::new("QUERY", "{}");
        assert_eq!(text(&one.on_local_message(&query, None).unwrap()), "one");
        assert_eq!(text(&two.on_local_message(&query, None).unwrap()), "two");
        assert_eq!(module.cache_stats().unwrap().semantic_merges, 0);
    }
}

#[test]
fn audited_state_preserves_dictionary_order_and_alias_topology() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.values = {}
        self.a = []
        self.b = []
    def on_message(self, msg, sender, ctx):
        self.values[sender] = True
    def on_local_message(self, msg, ctx):
        if msg.type == 'ALIAS':
            self.b = self.a
        elif msg.type == 'WRITE':
            self.a.append('x')
        ctx.send_local(Message('DELIVER', {'text': ''.join(self.values) + '/' + ''.join(self.b)}))
"#,
    );
    let module = fixture.module();
    let root = module.create("[]").unwrap();
    let mut ab = root.clone();
    let mut ba = root.clone();
    let msg = Message::new("X", "{}");
    ab.on_message(&msg, "a", None).unwrap();
    ab.on_message(&msg, "b", None).unwrap();
    ba.on_message(&msg, "b", None).unwrap();
    ba.on_message(&msg, "a", None).unwrap();
    assert_eq!(text(&ab.on_local_message(&msg, None).unwrap()), "ab/");
    assert_eq!(text(&ba.on_local_message(&msg, None).unwrap()), "ba/");
    let mut aliased = root.clone();
    let mut separate = root;
    aliased
        .on_local_message(&Message::new("ALIAS", "{}"), None)
        .unwrap();
    assert_eq!(
        text(
            &aliased
                .on_local_message(&Message::new("WRITE", "{}"), None)
                .unwrap()
        ),
        "/x"
    );
    assert_eq!(
        text(
            &separate
                .on_local_message(&Message::new("WRITE", "{}"), None)
                .unwrap()
        ),
        "/"
    );
}

#[test]
fn unsafe_python_keeps_history_cache_and_audited_unknown_objects_fall_back() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
import random
values = []
class Solution(Process):
    def __init__(self):
        self.objects = []
    def on_local_message(self, msg, ctx):
        values.append(random.random())
        self.objects.append(msg)
        ctx.send_local(Message('DELIVER', {'text': str(len(values)) + '/' + str(len(set(self.objects)))}))
"#,
    );
    let module = fixture.module();
    let mut process = module.create("[]").unwrap();
    let msg = Message::new("X", "{}");
    assert_eq!(text(&process.on_local_message(&msg, None).unwrap()), "1/1");
    assert_eq!(text(&process.on_local_message(&msg, None).unwrap()), "2/2");
    assert_eq!(module.cache_stats().unwrap().semantic_merges, 0);
    let unknown = Fixture::new(
        r#"
from anysystem import Process
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.value = object()
    def on_message(self, msg, sender, ctx):
        pass
"#,
    );
    let module = unknown.module();
    let mut process = module.create("[]").unwrap();
    process.on_message(&msg, "a", None).unwrap();
    process.on_message(&msg, "a", None).unwrap();
    assert_eq!(module.cache_stats().unwrap().semantic_merges, 0);
    assert_eq!(module.cache_stats().unwrap().states, 3);
}

#[test]
fn semantic_cache_disabled_has_identical_outputs() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.value = 0
    def on_local_message(self, msg, ctx):
        self.value = (self.value + 1) % 3
        ctx.send_local(Message('DELIVER', {'text': str(self.value)}))
"#,
    );
    let enabled = fixture.module();
    let disabled = fixture.options(PythonOptions {
        semantic_state_cache: false,
        ..PythonOptions::default()
    });
    let mut a = enabled.create("[]").unwrap();
    let mut b = disabled.create("[]").unwrap();
    for turn in 0..24 {
        let msg = Message::new(if turn % 4 == 0 { "Y" } else { "X" }, "{}");
        assert_eq!(
            a.on_local_message(&msg, None).unwrap(),
            b.on_local_message(&msg, None).unwrap()
        );
    }
    assert!(enabled.cache_stats().unwrap().semantic_merges > 0);
    assert_eq!(disabled.cache_stats().unwrap().semantic_merges, 0);
}

#[test]
fn audited_helper_records_and_same_line_lambda_code_are_distinguished() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
__must_state_cache__ = 'pure-value-v1'
class Record:
    def __init__(self):
        self.value = False
class Solution(Process):
    def __init__(self):
        self.record = Record()
    def on_local_message(self, msg, ctx):
        self.record.value = not self.record.value
        ctx.set_predicate((lambda msg: True) if msg.type == 'YES' else (lambda msg: False))
"#,
    );
    let module = fixture.module();
    let root = module.create("[]").unwrap();
    let mut yes = root.clone();
    let mut no = root;
    let query = Message::new("X", "{}");
    yes.on_local_message(&Message::new("YES", "{}"), None)
        .unwrap();
    no.on_local_message(&Message::new("NO", "{}"), None)
        .unwrap();
    assert!(yes
        .receive_predicate()
        .unwrap()
        .unwrap()
        .matches(&query)
        .unwrap());
    assert!(!no
        .receive_predicate()
        .unwrap()
        .unwrap()
        .matches(&query)
        .unwrap());
    yes.on_local_message(&Message::new("YES", "{}"), None)
        .unwrap();
    yes.on_local_message(&Message::new("YES", "{}"), None)
        .unwrap();
    assert!(module.cache_stats().unwrap().semantic_merges > 0);
}

#[test]
fn audited_closure_cell_aliases_are_observable_and_preserved() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
def pair():
    counter = 0
    def advance():
        nonlocal counter
        counter += 1
    def read():
        return counter
    return advance, read
class Solution(Process):
    def __init__(self):
        self.advance = None
        self.read = None
    def on_local_message(self, msg, ctx):
        if msg.type == 'SHARED':
            self.advance, self.read = pair()
        elif msg.type == 'SEPARATE':
            self.advance, _ = pair()
            _, self.read = pair()
        else:
            self.advance()
            ctx.send_local(Message('DELIVER', {'text': str(self.read())}))
"#,
    );
    let module = fixture.module();
    let root = module.create("[]").unwrap();
    let mut shared = root.clone();
    let mut separate = root;
    shared
        .on_local_message(&Message::new("SHARED", "{}"), None)
        .unwrap();
    separate
        .on_local_message(&Message::new("SEPARATE", "{}"), None)
        .unwrap();
    let tick = Message::new("TICK", "{}");
    assert_eq!(text(&shared.on_local_message(&tick, None).unwrap()), "1");
    assert_eq!(text(&separate.on_local_message(&tick, None).unwrap()), "0");
}

#[test]
fn audited_slotted_process_and_inherited_slotted_record_fall_back() {
    for declaration in [
        "class Solution(Process):\n    __slots__ = ('counter',)\n    def __init__(self):\n        self.counter = 0\n    def on_local_message(self, msg, ctx):\n        self.counter += 1\n        ctx.send_local(Message('DELIVER', {'text': str(self.counter)}))\n",
        "class Base:\n    __slots__ = ('counter',)\nclass Record(Base):\n    pass\nclass Solution(Process):\n    def __init__(self):\n        self.record = Record()\n        self.record.counter = 0\n    def on_local_message(self, msg, ctx):\n        self.record.counter += 1\n        ctx.send_local(Message('DELIVER', {'text': str(self.record.counter)}))\n",
    ] {
        let fixture = Fixture::new(&format!(
            "from anysystem import Process, Message\n__must_state_cache__ = 'pure-value-v1'\n{declaration}"
        ));
        let module = fixture.module();
        let mut process = module.create("[]").unwrap();
        let msg = Message::new("X", "{}");
        for counter in 1..=4 {
            assert_eq!(text(&process.on_local_message(&msg, None).unwrap()), counter.to_string());
        }
        assert_eq!(module.cache_stats().unwrap().semantic_merges, 0);
        assert_eq!(module.cache_stats().unwrap().states, 5);
    }
}

#[test]
fn audited_nan_signs_remain_distinct() {
    let fixture = Fixture::new(
        r#"
import math
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.x = 0.0
    def on_local_message(self, msg, ctx):
        if msg.type == 'SET':
            self.x = float(msg['value'])
        else:
            ctx.send_local(Message('DELIVER', {'text': str(math.copysign(1, self.x))}))
"#,
    );
    let module = fixture.module();
    let root = module.create("[]").unwrap();
    let mut positive = root.clone();
    let mut negative = root;
    positive
        .on_local_message(&Message::new("SET", r#"{"value":"nan"}"#), None)
        .unwrap();
    negative
        .on_local_message(&Message::new("SET", r#"{"value":"-nan"}"#), None)
        .unwrap();
    let query = Message::new("QUERY", "{}");
    assert_eq!(
        text(&positive.on_local_message(&query, None).unwrap()),
        "1.0"
    );
    assert_eq!(
        text(&negative.on_local_message(&query, None).unwrap()),
        "-1.0"
    );
}

#[test]
fn audited_local_record_classes_with_distinct_method_closures_fall_back() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
def make_record(answer):
    class Record:
        def read(self):
            return answer
    return Record()
class Solution(Process):
    def __init__(self):
        self.record = None
    def on_local_message(self, msg, ctx):
        if msg.type == 'SET':
            self.record = make_record(msg['value'])
        else:
            ctx.send_local(Message('DELIVER', {'text': self.record.read()}))
"#,
    );
    let module = fixture.module();
    let root = module.create("[]").unwrap();
    let mut first = root.clone();
    let mut second = root;
    first
        .on_local_message(&Message::new("SET", r#"{"value":"first"}"#), None)
        .unwrap();
    second
        .on_local_message(&Message::new("SET", r#"{"value":"second"}"#), None)
        .unwrap();
    let query = Message::new("QUERY", "{}");
    assert_eq!(
        text(&first.on_local_message(&query, None).unwrap()),
        "first"
    );
    assert_eq!(
        text(&second.on_local_message(&query, None).unwrap()),
        "second"
    );
    assert_eq!(module.cache_stats().unwrap().semantic_merges, 0);
}

#[test]
fn audited_nan_aliases_preserve_container_equality() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def __init__(self):
        self.a = self.b = 0.0
    def on_local_message(self, msg, ctx):
        if msg.type == 'SHARED':
            self.a = self.b = float('nan')
        elif msg.type == 'SEPARATE':
            self.a = float('nan')
            self.b = float('nan')
        else:
            ctx.send_local(Message('DELIVER', {'text': str([self.a] == [self.b])}))
"#,
    );
    let module = fixture.module();
    let root = module.create("[]").unwrap();
    let mut shared = root.clone();
    let mut separate = root;
    shared
        .on_local_message(&Message::new("SHARED", "{}"), None)
        .unwrap();
    separate
        .on_local_message(&Message::new("SEPARATE", "{}"), None)
        .unwrap();
    let query = Message::new("QUERY", "{}");
    assert_eq!(
        text(&shared.on_local_message(&query, None).unwrap()),
        "True"
    );
    assert_eq!(
        text(&separate.on_local_message(&query, None).unwrap()),
        "False"
    );
}

#[test]
fn audited_process_class_changes_fall_back() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process, Message
__must_state_cache__ = 'pure-value-v1'
class Solution(Process):
    def on_local_message(self, msg, ctx):
        if msg.type == 'SWITCH':
            self.__class__ = Alternate
        else:
            ctx.send_local(Message('DELIVER', {'text': 'original'}))
class Alternate(Process):
    def on_local_message(self, msg, ctx):
        ctx.send_local(Message('DELIVER', {'text': 'alternate'}))
"#,
    );
    let module = fixture.module();
    let mut process = module.create("[]").unwrap();
    process
        .on_local_message(&Message::new("SWITCH", "{}"), None)
        .unwrap();
    assert_eq!(
        text(
            &process
                .on_local_message(&Message::new("QUERY", "{}"), None)
                .unwrap()
        ),
        "alternate"
    );
    assert_eq!(module.cache_stats().unwrap().semantic_merges, 0);
}

#[test]
#[ignore = "warm shared Python receive-predicate contention benchmark"]
fn warmed_predicate_cache_contention() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def on_start(self, ctx):
        ctx.set_sender_predicate(lambda msg, sender: msg['value'] == 7 and sender == '0')
"#,
    );
    let module = fixture.module();
    let mut process = module.create("[]").unwrap();
    process.on_start(None).unwrap();
    let predicate = process.receive_predicate().unwrap().unwrap();
    assert!(predicate
        .matches_parts_from("DATA", r#"{"value":7}"#, "0")
        .unwrap());
    for threads in [1, 12] {
        let barrier = std::sync::Barrier::new(threads);
        let start = Instant::now();
        std::thread::scope(|scope| {
            for _ in 0..threads {
                let predicate = &predicate;
                let barrier = &barrier;
                scope.spawn(move || {
                    barrier.wait();
                    for _ in 0..250_000 {
                        std::hint::black_box(
                            predicate
                                .matches_parts_from("DATA", r#"{"value":7}"#, "0")
                                .unwrap(),
                        );
                    }
                });
            }
        });
        eprintln!(
            "warmed predicates: threads={threads}, queries={}, elapsed={:?}",
            threads * 250_000,
            start.elapsed()
        );
    }
}

#[test]
fn predicate_front_keeps_opposite_module_and_snapshot_answers_separate_across_threads() {
    let fixture = Fixture::new(
        r#"
from anysystem import Process
class Solution(Process):
    def __init__(self, answer):
        self.answer = answer
    def on_start(self, ctx):
        ctx.set_sender_predicate(lambda msg, sender: self.answer if sender == '0' else not self.answer)
    def on_local_message(self, msg, ctx):
        self.answer = not self.answer
        ctx.set_sender_predicate(lambda msg, sender: self.answer if sender == '0' else not self.answer)
"#,
    );
    let first_module = fixture.module();
    let second_module = fixture.module();
    let mut first = first_module.create("[true]").unwrap();
    let mut second = second_module.create("[false]").unwrap();
    first.on_start(None).unwrap();
    second.on_start(None).unwrap();
    let original = first.receive_predicate().unwrap().unwrap();
    first
        .on_local_message(&Message::new("FLIP", "{}"), None)
        .unwrap();
    let flipped = first.receive_predicate().unwrap().unwrap();
    let opposite_module = second.receive_predicate().unwrap().unwrap();
    std::thread::scope(|scope| {
        for _ in 0..12 {
            let (original, flipped, opposite_module) = (&original, &flipped, &opposite_module);
            scope.spawn(move || {
                for _ in 0..100 {
                    for sender in ["0", "1"] {
                        let expected = sender == "0";
                        assert_eq!(
                            original.matches_parts_from("DATA", "{}", sender).unwrap(),
                            expected
                        );
                        assert_eq!(
                            flipped.matches_parts_from("DATA", "{}", sender).unwrap(),
                            !expected
                        );
                        assert_eq!(
                            opposite_module
                                .matches_parts_from("DATA", "{}", sender)
                                .unwrap(),
                            !expected
                        );
                    }
                }
            });
        }
    });
}
