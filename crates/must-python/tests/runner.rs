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
fn cache_hits_continue_while_python_miss_is_running() {
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
    let module = fixture.module();
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
        std::fs::write(fixture.0.join("finish"), "").unwrap();
        assert_eq!(text(&actions), "cached");
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
