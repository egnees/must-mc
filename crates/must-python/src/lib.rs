//! Run AnySystem-style Python callbacks with deterministic local-history replay.
//!
//! Process clones are independent history cursors. A module shares one persistent
//! interpreter and caches transitions, so repeated Must replays stay in Rust.
//! Cache misses recreate the solution module and replay the local callback history;
//! no Python object needs to be pickleable. Outputs of replayed callbacks are checked.
//!
//! The modeled program uses a fixed Python hash seed and reproducible `random`,
//! unseeded `random.Random`, and `uuid.uuid4` streams derived per constructor from
//! the configured seed and arguments. This explores one random
//! trace, not all random choices. External I/O, clocks outside `Context.time`, and
//! mutation of interpreter internals are outside this deterministic model. This is
//! a runner for trusted submissions, not an operating-system security sandbox.
mod json;

use json::{parse, quote, Json};
use std::collections::BTreeMap;
use std::fmt;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::{mpsc, Arc, Mutex, RwLock};
use std::time::Duration;

const MAX_FRAME: usize = 8 * 1024 * 1024;

#[derive(Clone, Debug)]
pub struct PythonOptions {
    pub python: PathBuf,
    /// Wall-clock limit for each cache miss, including import and history replay.
    pub timeout: Duration,
    /// Maximum number of distinct constructor/transition history nodes.
    pub max_states: usize,
    pub seed: u64,
}

impl Default for PythonOptions {
    fn default() -> Self {
        Self {
            python: "python3".into(),
            timeout: Duration::from_secs(5),
            max_states: 100_000,
            seed: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    Unsupported,
    Execution,
    Resource,
    Transport,
}

#[derive(Clone, Debug)]
pub struct Error {
    kind: ErrorKind,
    message: String,
}
impl Error {
    fn new(kind: ErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Error {}
impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Self::new(ErrorKind::Transport, value.to_string())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Message {
    pub kind: String,
    pub data: String,
}
impl Message {
    pub fn new(kind: impl Into<String>, data: impl Into<String>) -> Self {
        Self {
            kind: kind.into(),
            data: data.into(),
        }
    }
    /// Read a string from the top-level JSON object. Missing keys return `None`;
    /// malformed JSON and present non-string fields return an error.
    pub fn string_field(&self, key: &str) -> Result<Option<String>, Error> {
        match parse(&self.data)? {
            Json::Object(object) => object
                .get(key)
                .map(|v| v.string().map(str::to_owned))
                .transpose(),
            _ => Err(Error::new(
                ErrorKind::Execution,
                "message data must be a JSON object",
            )),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Action {
    Send {
        to: String,
        message: Message,
    },
    Local {
        message: Message,
    },
    SetTimer {
        name: String,
        delay: f64,
        once: bool,
    },
    CancelTimer {
        name: String,
    },
}

/// A loaded solution and its shared, synchronized transition cache.
#[derive(Clone)]
pub struct PythonModule {
    inner: Arc<ModuleInner>,
}
struct ModuleInner {
    worker: Mutex<Worker>,
    cache: RwLock<Cache>,
    max_states: usize,
}
type Transition = (usize, Arc<[Action]>);
#[derive(Default)]
struct Cache {
    constructors: BTreeMap<String, usize>,
    transitions: BTreeMap<usize, Vec<(Callback, Transition)>>,
    states: usize,
}
impl Cache {
    fn transition(&self, state: usize, event: &CallbackRef<'_>) -> Option<Transition> {
        let edges = self.transitions.get(&state)?;
        let index = edges
            .binary_search_by(|(stored, _)| event.compare(stored).reverse())
            .ok()?;
        Some(edges[index].1.clone())
    }
    fn insert_transition(&mut self, state: usize, event: Callback, transition: Transition) {
        let edges = self.transitions.entry(state).or_default();
        let index = edges
            .binary_search_by(|(stored, _)| stored.cmp(&event))
            .unwrap_err();
        edges.insert(index, (event, transition));
    }
    fn capacity(&self, max_states: usize) -> Result<(), Error> {
        if self.states >= max_states {
            Err(Error::new(
                ErrorKind::Resource,
                format!("Python state limit ({max_states}) exceeded"),
            ))
        } else {
            Ok(())
        }
    }
}
impl PythonModule {
    pub fn new(
        path: impl AsRef<Path>,
        class_name: &str,
        options: PythonOptions,
    ) -> Result<Self, Error> {
        let path = path.as_ref().canonicalize()?;
        let mut worker = Worker::new(&path, class_name, &options)?;
        worker.request("{\"op\":\"init\"}".to_owned())?;
        Ok(Self {
            inner: Arc::new(ModuleInner {
                worker: Mutex::new(worker),
                cache: RwLock::new(Cache::default()),
                max_states: options.max_states,
            }),
        })
    }

    /// `args_json` is a JSON array of positional constructor arguments.
    pub fn create(&self, args_json: &str) -> Result<PythonProcess, Error> {
        bounded(args_json)?;
        let cached = self.read_cache()?.constructors.get(args_json).copied();
        if let Some(state) = cached {
            return Ok(PythonProcess {
                module: self.clone(),
                state,
            });
        }
        parse(args_json)?.array()?;
        // Cache misses serialize on the interpreter. Never hold the cache lock
        // while waiting for Python: other model-checking threads can use hits.
        let mut worker = self.lock_worker()?;
        let cached = self.read_cache()?.constructors.get(args_json).copied();
        if let Some(state) = cached {
            return Ok(PythonProcess {
                module: self.clone(),
                state,
            });
        }
        self.read_cache()?.capacity(self.inner.max_states)?;
        let result = worker.request(format!(
            "{{\"op\":\"create\",\"args\":{}}}",
            quote(args_json)
        ))?;
        let state = state_id(&result)?;
        let mut cache = self.write_cache()?;
        cache.states += 1;
        cache.constructors.insert(args_json.to_owned(), state);
        Ok(PythonProcess {
            module: self.clone(),
            state,
        })
    }

    fn lock_worker(&self) -> Result<std::sync::MutexGuard<'_, Worker>, Error> {
        self.inner
            .worker
            .lock()
            .map_err(|_| Error::new(ErrorKind::Transport, "Python worker lock poisoned"))
    }
    fn read_cache(&self) -> Result<std::sync::RwLockReadGuard<'_, Cache>, Error> {
        self.inner
            .cache
            .read()
            .map_err(|_| Error::new(ErrorKind::Transport, "Python cache lock poisoned"))
    }
    fn write_cache(&self) -> Result<std::sync::RwLockWriteGuard<'_, Cache>, Error> {
        self.inner
            .cache
            .write()
            .map_err(|_| Error::new(ErrorKind::Transport, "Python cache lock poisoned"))
    }
}

/// Cheaply cloneable local state cursor. Clones branch without sharing mutable
/// Python process state, while identical callback prefixes share cached results.
#[derive(Clone)]
pub struct PythonProcess {
    module: PythonModule,
    state: usize,
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Callback {
    method: &'static str,
    time: Option<u64>,
    message: Option<Message>,
    argument: Option<String>,
}
struct CallbackRef<'a> {
    method: &'static str,
    time: Option<u64>,
    message: Option<&'a Message>,
    argument: Option<&'a str>,
}
impl<'a> CallbackRef<'a> {
    fn new(
        method: &'static str,
        time: Option<f64>,
        message: Option<&'a Message>,
        argument: Option<&'a str>,
    ) -> Result<Self, Error> {
        if time.is_some_and(|t| !t.is_finite()) {
            return Err(Error::new(
                ErrorKind::Execution,
                "callback time must be finite",
            ));
        }
        if let Some(message) = message {
            bounded(&message.data)?;
        }
        Ok(Self {
            method,
            time: time.map(f64::to_bits),
            message,
            argument,
        })
    }
    fn compare(&self, other: &Callback) -> std::cmp::Ordering {
        self.method
            .cmp(other.method)
            .then_with(|| self.time.cmp(&other.time))
            .then_with(|| self.message.cmp(&other.message.as_ref()))
            .then_with(|| self.argument.cmp(&other.argument.as_deref()))
    }
    fn owned(&self) -> Callback {
        Callback {
            method: self.method,
            time: self.time,
            message: self.message.cloned(),
            argument: self.argument.map(str::to_owned),
        }
    }
}
impl Callback {
    fn encode(&self) -> Result<String, Error> {
        let time = clock(self.time.map(f64::from_bits))?;
        let event = if let Some(message) = &self.message {
            format!(
                "{{\"method\":{},\"time\":{},\"kind\":{},\"data\":{},\"sender\":{}}}",
                quote(self.method),
                time,
                quote(&message.kind),
                quote(&message.data),
                self.argument
                    .as_deref()
                    .map_or_else(|| "null".to_owned(), quote)
            )
        } else if self.method == "on_timer" {
            format!(
                "{{\"method\":\"on_timer\",\"time\":{},\"name\":{}}}",
                time,
                quote(self.argument.as_deref().unwrap())
            )
        } else {
            format!("{{\"method\":\"on_start\",\"time\":{}}}", time)
        };
        bounded(&event)?;
        Ok(event)
    }
}

impl PythonProcess {
    pub fn on_start(&mut self, time: Option<f64>) -> Result<Vec<Action>, Error> {
        self.on_start_shared(time).map(|actions| actions.to_vec())
    }
    pub fn on_start_shared(&mut self, time: Option<f64>) -> Result<Arc<[Action]>, Error> {
        self.step(CallbackRef::new("on_start", time, None, None)?)
    }
    pub fn on_local_message(
        &mut self,
        message: &Message,
        time: Option<f64>,
    ) -> Result<Vec<Action>, Error> {
        self.on_local_message_shared(message, time)
            .map(|actions| actions.to_vec())
    }
    pub fn on_local_message_shared(
        &mut self,
        message: &Message,
        time: Option<f64>,
    ) -> Result<Arc<[Action]>, Error> {
        self.step(CallbackRef::new(
            "on_local_message",
            time,
            Some(message),
            None,
        )?)
    }
    pub fn on_message(
        &mut self,
        message: &Message,
        sender: &str,
        time: Option<f64>,
    ) -> Result<Vec<Action>, Error> {
        self.on_message_shared(message, sender, time)
            .map(|actions| actions.to_vec())
    }
    pub fn on_message_shared(
        &mut self,
        message: &Message,
        sender: &str,
        time: Option<f64>,
    ) -> Result<Arc<[Action]>, Error> {
        self.step(CallbackRef::new(
            "on_message",
            time,
            Some(message),
            Some(sender),
        )?)
    }
    pub fn on_timer(&mut self, name: &str, time: Option<f64>) -> Result<Vec<Action>, Error> {
        self.on_timer_shared(name, time)
            .map(|actions| actions.to_vec())
    }
    pub fn on_timer_shared(
        &mut self,
        name: &str,
        time: Option<f64>,
    ) -> Result<Arc<[Action]>, Error> {
        self.step(CallbackRef::new("on_timer", time, None, Some(name))?)
    }
    fn step(&mut self, event: CallbackRef<'_>) -> Result<Arc<[Action]>, Error> {
        let previous_state = self.state;
        let cached = self.module.read_cache()?.transition(previous_state, &event);
        if let Some((state, actions)) = cached {
            self.state = state;
            return Ok(actions);
        }
        let mut worker = self.module.lock_worker()?;
        let cached = self.module.read_cache()?.transition(previous_state, &event);
        if let Some((state, actions)) = cached {
            drop(worker);
            self.state = state;
            return Ok(actions);
        }
        self.module
            .read_cache()?
            .capacity(self.module.inner.max_states)?;
        if let Some(message) = &event.message {
            parse(&message.data)?;
        }
        let owned = event.owned();
        let encoded = owned.encode()?;
        let result = worker.request(format!(
            "{{\"op\":\"step\",\"state\":{},\"event\":{}}}",
            self.state, encoded
        ))?;
        let state = state_id(&result)?;
        let actions: Arc<[Action]> = decode_actions(result.field("actions")?)?.into();
        let mut cache = self.module.write_cache()?;
        cache.states += 1;
        cache.insert_transition(previous_state, owned, (state, actions.clone()));
        self.state = state;
        Ok(actions)
    }
}

fn clock(time: Option<f64>) -> Result<String, Error> {
    match time {
        None => Ok("null".to_owned()),
        Some(t) if t.is_finite() => Ok(t.to_string()),
        _ => Err(Error::new(
            ErrorKind::Execution,
            "callback time must be finite",
        )),
    }
}
fn state_id(result: &Json) -> Result<usize, Error> {
    result
        .field("state")?
        .number()?
        .parse()
        .map_err(|_| Error::new(ErrorKind::Transport, "invalid worker state id"))
}
fn bounded(payload: &str) -> Result<(), Error> {
    if payload.len() > MAX_FRAME {
        Err(Error::new(
            ErrorKind::Resource,
            "Python protocol frame limit exceeded",
        ))
    } else {
        Ok(())
    }
}
fn decode_actions(value: &Json) -> Result<Vec<Action>, Error> {
    value
        .array()?
        .iter()
        .map(|action| {
            let string = |key| action.field(key)?.string().map(str::to_owned);
            let message = || -> Result<Message, Error> {
                let m = action.field("message")?;
                Ok(Message::new(
                    m.field("kind")?.string()?,
                    m.field("data")?.string()?,
                ))
            };
            match action.field("op")?.string()? {
                "send" => Ok(Action::Send {
                    to: string("to")?,
                    message: message()?,
                }),
                "local" => Ok(Action::Local {
                    message: message()?,
                }),
                "cancel" => Ok(Action::CancelTimer {
                    name: string("name")?,
                }),
                "timer" => {
                    let delay: f64 = action
                        .field("delay")?
                        .number()?
                        .parse()
                        .map_err(|_| Error::new(ErrorKind::Transport, "invalid timer delay"))?;
                    let once = match action.field("once")? {
                        Json::Bool(b) => *b,
                        _ => {
                            return Err(Error::new(ErrorKind::Transport, "invalid timer once flag"))
                        }
                    };
                    Ok(Action::SetTimer {
                        name: string("name")?,
                        delay,
                        once,
                    })
                }
                _ => Err(Error::new(ErrorKind::Transport, "unknown worker action")),
            }
        })
        .collect()
}

struct Worker {
    child: Child,
    commands: mpsc::Sender<String>,
    replies: mpsc::Receiver<Result<String, Error>>,
    timeout: Duration,
    stopped: bool,
}
impl Worker {
    fn new(path: &Path, class_name: &str, options: &PythonOptions) -> Result<Self, Error> {
        let mut child = Command::new(&options.python)
            .arg("-u")
            .arg("-c")
            .arg(include_str!("worker.py"))
            .arg(path)
            .arg(class_name)
            .arg(options.seed.to_string())
            .arg(include_str!("anysystem.py"))
            .env("PYTHONHASHSEED", (options.seed as u32).to_string())
            .env("PYTHONDONTWRITEBYTECODE", "1")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let mut stdin = child
            .stdin
            .take()
            .ok_or_else(|| Error::new(ErrorKind::Transport, "missing worker stdin"))?;
        let mut stdout = child
            .stdout
            .take()
            .ok_or_else(|| Error::new(ErrorKind::Transport, "missing worker stdout"))?;
        let (commands, incoming) = mpsc::channel::<String>();
        let (outgoing, replies) = mpsc::channel();
        // Both writing and reading happen here: a large request cannot block the
        // caller past its deadline if a Python callback has stopped reading.
        let spawned = std::thread::Builder::new()
            .name("must-python-io".into())
            .spawn(move || {
                while let Ok(request) = incoming.recv() {
                    let result = (|| -> Result<String, Error> {
                        stdin.write_all(&(request.len() as u32).to_be_bytes())?;
                        stdin.write_all(request.as_bytes())?;
                        stdin.flush()?;
                        let mut length = [0; 4];
                        stdout.read_exact(&mut length)?;
                        let length = u32::from_be_bytes(length) as usize;
                        if length > MAX_FRAME {
                            return Err(Error::new(
                                ErrorKind::Resource,
                                "Python response frame limit exceeded",
                            ));
                        }
                        let mut data = vec![0; length];
                        stdout.read_exact(&mut data)?;
                        String::from_utf8(data).map_err(|_| {
                            Error::new(ErrorKind::Transport, "invalid UTF-8 from Python worker")
                        })
                    })();
                    let failed = result.is_err();
                    if outgoing.send(result).is_err() || failed {
                        break;
                    }
                }
            });
        if let Err(error) = spawned {
            let _ = child.kill();
            let _ = child.wait();
            return Err(error.into());
        }
        Ok(Self {
            child,
            commands,
            replies,
            timeout: options.timeout,
            stopped: false,
        })
    }
    fn stop(&mut self) {
        if !self.stopped {
            let _ = self.child.kill();
            let _ = self.child.wait();
            self.stopped = true;
        }
    }
    fn request(&mut self, request: String) -> Result<Json, Error> {
        bounded(&request)?;
        if self.stopped {
            return Err(Error::new(
                ErrorKind::Transport,
                "Python worker was stopped",
            ));
        }
        if self.commands.send(request).is_err() {
            self.stop();
            return Err(Error::new(
                ErrorKind::Transport,
                "Python worker transport closed",
            ));
        }
        let text = match self.replies.recv_timeout(self.timeout) {
            Ok(Ok(text)) => text,
            Ok(Err(error)) => {
                self.stop();
                return Err(error);
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                self.stop();
                return Err(Error::new(
                    ErrorKind::Resource,
                    format!("Python callback/replay exceeded {:?}", self.timeout),
                ));
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                self.stop();
                return Err(Error::new(
                    ErrorKind::Transport,
                    "Python worker disconnected",
                ));
            }
        };
        let result = parse(&text)?;
        match result.field("ok")? {
            Json::Bool(true) => Ok(result),
            Json::Bool(false) => {
                let kind = match result.field("kind")?.string()? {
                    "unsupported" => ErrorKind::Unsupported,
                    "resource" => ErrorKind::Resource,
                    _ => ErrorKind::Execution,
                };
                Err(Error::new(kind, result.field("error")?.string()?))
            }
            _ => Err(Error::new(ErrorKind::Transport, "invalid worker response")),
        }
    }
}
impl Drop for Worker {
    fn drop(&mut self) {
        self.stop();
    }
}
