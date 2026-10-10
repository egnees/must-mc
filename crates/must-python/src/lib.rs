//! Run AnySystem-style Python callbacks with deterministic local-history replay.
//!
//! Process clones are independent history cursors. A module shares one persistent
//! interpreter pool and caches transitions, so repeated Must replays stay in Rust.
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
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{mpsc, Arc, Mutex, RwLock, Weak};
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
    /// Independent interpreters available for concurrent cache misses.
    pub workers: usize,
    /// Intern value states only for explicitly audited pure-value-v1 modules.
    /// Arbitrary Python keeps the deterministic history cache. This never prunes
    /// executions: every repeated callback still returns its actions.
    pub semantic_state_cache: bool,
}

impl Default for PythonOptions {
    fn default() -> Self {
        Self {
            python: "python3".into(),
            timeout: Duration::from_secs(5),
            max_states: 100_000,
            seed: 0,
            workers: 1,
            semantic_state_cache: true,
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
    workers: Vec<Mutex<Worker>>,
    assignments: Mutex<Vec<(std::thread::ThreadId, usize)>>,
    cache: RwLock<Cache>,
    max_states: usize,
    transition_hits: AtomicU64,
    transition_misses: AtomicU64,
    semantic_merges: AtomicU64,
}

/// Cache counters shared across the interpreter pool.
#[derive(Clone, Copy, Debug, Default)]
pub struct PythonCacheStats {
    pub transition_hits: u64,
    pub transition_misses: u64,
    pub semantic_merges: u64,
    pub states: usize,
}

type Transition = (usize, Arc<[Action]>);
#[derive(Default)]
struct Cache {
    constructors: BTreeMap<String, usize>,
    transitions: BTreeMap<usize, Vec<(Callback, Transition)>>,
    histories: Vec<History>,
    semantic_states: BTreeMap<String, usize>,
}
struct History {
    parent: Option<usize>,
    encoded: Arc<str>,
    owner: usize,
    predicate: Option<Arc<PredicateCache>>,
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
        if self.histories.len() >= max_states {
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
        if options.workers == 0 {
            return Err(Error::new(
                ErrorKind::Resource,
                "Python workers must be positive",
            ));
        }
        let mut workers = Vec::with_capacity(options.workers);
        for index in 0..options.workers {
            let mut worker = Worker::new(&path, class_name, &options)?;
            worker.index = index;
            worker.request("{\"op\":\"init\"}".to_owned())?;
            workers.push(Mutex::new(worker));
        }
        Ok(Self {
            inner: Arc::new(ModuleInner {
                workers,
                assignments: Mutex::new(Vec::new()),
                cache: RwLock::new(Cache::default()),
                max_states: options.max_states,
                transition_hits: AtomicU64::new(0),
                transition_misses: AtomicU64::new(0),
                semantic_merges: AtomicU64::new(0),
            }),
        })
    }

    pub fn cache_stats(&self) -> Result<PythonCacheStats, Error> {
        Ok(PythonCacheStats {
            transition_hits: self.inner.transition_hits.load(Ordering::Relaxed),
            transition_misses: self.inner.transition_misses.load(Ordering::Relaxed),
            semantic_merges: self.inner.semantic_merges.load(Ordering::Relaxed),
            states: self.read_cache()?.histories.len(),
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
        // Cache hits never wait for an interpreter.
        let mut worker = self.lock_worker()?;
        {
            let cache = self.read_cache()?;
            if let Some(&state) = cache.constructors.get(args_json) {
                return Ok(PythonProcess {
                    module: self.clone(),
                    state,
                });
            }
            cache.capacity(self.inner.max_states)?;
        }
        let result = worker.request(format!(
            "{{\"op\":\"create\",\"args\":{}}}",
            quote(args_json)
        ))?;
        let local_state = state_id(&result)?;
        let mut cache = self.write_cache()?;
        let state = if let Some(&state) = cache.constructors.get(args_json) {
            state
        } else {
            cache.capacity(self.inner.max_states)?;
            let state = cache.histories.len();
            cache.histories.push(History {
                parent: None,
                predicate: None,
                owner: worker.index,
                encoded: format!("{{\"args\":{}}}", quote(args_json)).into(),
            });
            if let Some(key) = semantic_key(&result)? {
                cache.semantic_states.insert(key.to_owned(), state);
            }
            cache.constructors.insert(args_json.to_owned(), state);
            state
        };
        worker.states.insert(state, local_state);
        Ok(PythonProcess {
            module: self.clone(),
            state,
        })
    }

    fn history_request<'a>(
        &'a self,
        state: usize,
        op: &str,
        extra: &str,
        mut worker: std::sync::MutexGuard<'a, Worker>,
    ) -> Result<(std::sync::MutexGuard<'a, Worker>, Json), Error> {
        let op = quote(op);
        let mut missing = Vec::new();
        let mut cursor = Some(state);
        {
            let cache = self.read_cache()?;
            while let Some(state) = cursor {
                if worker.states.contains_key(&state) {
                    break;
                }
                let history = &cache.histories[state];
                missing.push((state, history.encoded.clone()));
                cursor = history.parent;
            }
        }
        missing.reverse();
        let imported_size = missing
            .iter()
            .try_fold(0usize, |size, (_, node)| size.checked_add(node.len() + 1));
        let request = if imported_size
            .is_none_or(|size| size.saturating_add(extra.len()).saturating_add(128) > MAX_FRAME)
        {
            // Long histories remain usable without creating an oversized import frame.
            let owner = self.read_cache()?.histories[state].owner;
            drop(worker);
            worker = self.inner.workers[owner]
                .lock()
                .map_err(|_| Error::new(ErrorKind::Transport, "Python worker lock poisoned"))?;
            missing.clear();
            let local = worker.states[&state];
            format!("{{\"op\":{op},\"state\":{local},\"import\":[],{extra}}}")
        } else {
            let base = cursor.map_or_else(
                || "null".to_owned(),
                |state| worker.states[&state].to_string(),
            );
            let mut request = format!("{{\"op\":{op},\"state\":{base},\"import\":[");
            for (index, (_, node)) in missing.iter().enumerate() {
                if index != 0 {
                    request.push(',');
                }
                request.push_str(node);
            }
            request.push_str(&format!("],{extra}}}"));
            request
        };
        let result = worker.request(request)?;
        let imported = result.field("imported")?.array()?;
        if imported.len() != missing.len() {
            return Err(Error::new(
                ErrorKind::Transport,
                "invalid imported history length",
            ));
        }
        for ((global, _), local) in missing.iter().zip(imported) {
            let local = local
                .number()?
                .parse()
                .map_err(|_| Error::new(ErrorKind::Transport, "invalid imported state id"))?;
            worker.states.insert(*global, local);
        }
        Ok((worker, result))
    }

    fn lock_worker(&self) -> Result<std::sync::MutexGuard<'_, Worker>, Error> {
        let thread = std::thread::current().id();
        let mut assignments = self.inner.assignments.lock().map_err(|_| {
            Error::new(
                ErrorKind::Transport,
                "Python worker assignments lock poisoned",
            )
        })?;
        let index = if let Some((_, index)) = assignments.iter().find(|(id, _)| *id == thread) {
            *index
        } else {
            let index = assignments.len() % self.inner.workers.len();
            assignments.push((thread, index));
            index
        };
        drop(assignments);
        self.inner.workers[index]
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
    pub fn receive_predicate(&self) -> Result<Option<PythonReceivePredicate>, Error> {
        Ok(self.module.read_cache()?.histories[self.state]
            .predicate
            .as_ref()
            .map(|cache| PythonReceivePredicate {
                module: self.module.clone(),
                state: self.state,
                cache: cache.clone(),
            }))
    }

    fn step(&mut self, event: CallbackRef<'_>) -> Result<Arc<[Action]>, Error> {
        let previous_state = self.state;
        let cached = self.module.read_cache()?.transition(previous_state, &event);
        if let Some((state, actions)) = cached {
            self.module
                .inner
                .transition_hits
                .fetch_add(1, Ordering::Relaxed);
            self.state = state;
            return Ok(actions);
        }
        let worker = self.module.lock_worker()?;
        {
            let cache = self.module.read_cache()?;
            if let Some((state, actions)) = cache.transition(previous_state, &event) {
                self.module
                    .inner
                    .transition_hits
                    .fetch_add(1, Ordering::Relaxed);
                self.state = state;
                return Ok(actions);
            }
        }
        if let Some(message) = &event.message {
            parse(&message.data)?;
        }
        self.module
            .inner
            .transition_misses
            .fetch_add(1, Ordering::Relaxed);
        let owned = event.owned();
        let encoded = owned.encode()?;
        let (mut worker, result) = self.module.history_request(
            previous_state,
            "step",
            &format!("\"event\":{encoded}"),
            worker,
        )?;
        let local_state = state_id(&result)?;
        let has_predicate = json_bool(result.field("has_predicate")?)?;
        let mut actions: Arc<[Action]> = decode_actions(result.field("actions")?)?.into();
        let expected = encode_json(result.field("actions")?);
        let mut cache = self.module.write_cache()?;
        let state = if let Some((state, cached_actions)) = cache.transition(previous_state, &event)
        {
            if cached_actions != actions
                || cache.histories[state].predicate.is_some() != has_predicate
            {
                return Err(Error::new(
                    ErrorKind::Execution,
                    "nondeterministic Python replay: concurrent callback outputs changed",
                ));
            }
            actions = cached_actions;
            state
        } else {
            let key = semantic_key(&result)?;
            let existing = key.and_then(|key| cache.semantic_states.get(key).copied());
            let state = if let Some(state) = existing {
                if cache.histories[state].predicate.is_some() != has_predicate {
                    return Err(Error::new(
                        ErrorKind::Execution,
                        "invalid semantic predicate state",
                    ));
                }
                self.module
                    .inner
                    .semantic_merges
                    .fetch_add(1, Ordering::Relaxed);
                state
            } else {
                cache.capacity(self.module.inner.max_states)?;
                let state = cache.histories.len();
                cache.histories.push(History {
                    parent: Some(previous_state),
                    predicate: has_predicate.then(|| Arc::new(PredicateCache::default())),
                    owner: worker.index,
                    encoded: format!(
                        "{{\"event\":{encoded},\"expected\":[{expected},{has_predicate}]}}"
                    )
                    .into(),
                });
                if let Some(key) = key {
                    cache.semantic_states.insert(key.to_owned(), state);
                }
                state
            };
            cache.insert_transition(previous_state, owned, (state, actions.clone()));
            state
        };
        // Keep the first representative history when semantic interning returns
        // an existing state (including self-loops). Import chains remain acyclic
        // and cache misses replay the short representative, never a cyclic path.
        worker.states.entry(state).or_insert(local_state);
        self.state = state;
        Ok(actions)
    }
}

type PredicateQuery = (Message, Option<String>);
type PredicateResults = Vec<(PredicateQuery, bool)>;

const PREDICATE_FRONT_SLOTS: usize = 128;
const PREDICATE_FRONT_QUERIES: usize = 64;
const PREDICATE_FRONT_BYTES: usize = 16 * 1024;

#[derive(Default)]
struct PredicateFrontEntry {
    // A weak owner retains allocation metadata, preventing pointer reuse (ABA)
    // without extending the lifetime of the shared cache's potentially large
    // result vector. Comparing pointers never dereferences a dropped owner.
    owner: Option<Weak<PredicateCache>>,
    results: PredicateResults,
    bytes: usize,
}

struct PredicateFront {
    slots: [PredicateFrontEntry; PREDICATE_FRONT_SLOTS],
}
impl Default for PredicateFront {
    fn default() -> Self {
        Self {
            slots: std::array::from_fn(|_| PredicateFrontEntry::default()),
        }
    }
}

fn predicate_query_index(
    results: &PredicateResults,
    kind: &str,
    data: &str,
    sender: Option<&str>,
) -> Result<usize, usize> {
    results.binary_search_by(|(message, _)| {
        (
            message.0.kind.as_str(),
            message.0.data.as_str(),
            message.1.as_deref(),
        )
            .cmp(&(kind, data, sender))
    })
}

impl PredicateFront {
    fn slot(owner: &Arc<PredicateCache>) -> usize {
        let address = Arc::as_ptr(owner) as usize;
        ((address >> 4) ^ (address >> 12)) % PREDICATE_FRONT_SLOTS
    }

    fn lookup(
        &self,
        owner: &Arc<PredicateCache>,
        kind: &str,
        data: &str,
        sender: Option<&str>,
    ) -> Option<bool> {
        let entry = &self.slots[Self::slot(owner)];
        if !entry
            .owner
            .as_ref()
            .is_some_and(|stored| stored.as_ptr() == Arc::as_ptr(owner))
        {
            return None;
        }
        predicate_query_index(&entry.results, kind, data, sender)
            .ok()
            .map(|index| entry.results[index].1)
    }

    fn insert(
        &mut self,
        owner: &Arc<PredicateCache>,
        kind: &str,
        data: &str,
        sender: Option<&str>,
        accepted: bool,
    ) {
        // Large queries still use the exact shared cache, without duplicating
        // their payloads into every exploration worker's front cache.
        let bytes = kind
            .len()
            .saturating_add(data.len())
            .saturating_add(sender.map_or(0, str::len));
        if bytes > PREDICATE_FRONT_BYTES {
            return;
        }
        let entry = &mut self.slots[Self::slot(owner)];
        if !entry
            .owner
            .as_ref()
            .is_some_and(|stored| stored.as_ptr() == Arc::as_ptr(owner))
        {
            entry.owner = Some(Arc::downgrade(owner));
            entry.results.clear();
            entry.bytes = 0;
        }
        let Err(mut index) = predicate_query_index(&entry.results, kind, data, sender) else {
            return;
        };
        if entry.results.len() == PREDICATE_FRONT_QUERIES
            || entry.bytes + bytes > PREDICATE_FRONT_BYTES
        {
            entry.results.clear();
            entry.bytes = 0;
            index = 0;
        }
        entry.results.insert(
            index,
            (
                (Message::new(kind, data), sender.map(str::to_owned)),
                accepted,
            ),
        );
        entry.bytes += bytes;
    }
}

thread_local! {
    static PREDICATE_FRONT: RefCell<PredicateFront> = RefCell::new(PredicateFront::default());
}

#[derive(Default)]
struct PredicateCache {
    results: RwLock<PredicateResults>,
    miss: Mutex<()>,
}
impl PredicateCache {
    fn lookup(&self, kind: &str, data: &str, sender: Option<&str>) -> Result<Option<bool>, Error> {
        let results = self.results.read().map_err(|_| {
            Error::new(ErrorKind::Transport, "Python predicate cache lock poisoned")
        })?;
        Ok(predicate_query_index(&results, kind, data, sender)
            .ok()
            .map(|index| results[index].1))
    }
}

/// An immutable receive predicate evaluated against its original local history.
#[derive(Clone)]
pub struct PythonReceivePredicate {
    module: PythonModule,
    state: usize,
    cache: Arc<PredicateCache>,
}
impl PythonReceivePredicate {
    pub fn matches(&self, message: &Message) -> Result<bool, Error> {
        self.matches_parts(&message.kind, &message.data)
    }

    pub fn matches_parts(&self, kind: &str, data: &str) -> Result<bool, Error> {
        self.matches_parts_with_sender(kind, data, None)
    }

    pub fn matches_parts_from(&self, kind: &str, data: &str, sender: &str) -> Result<bool, Error> {
        self.matches_parts_with_sender(kind, data, Some(sender))
    }

    fn matches_parts_with_sender(
        &self,
        kind: &str,
        data: &str,
        sender: Option<&str>,
    ) -> Result<bool, Error> {
        if let Some(accepted) =
            PREDICATE_FRONT.with(|front| front.borrow().lookup(&self.cache, kind, data, sender))
        {
            return Ok(accepted);
        }
        // No TLS borrow crosses the shared locks or a Python worker request.
        // Failed evaluations never enter either front-cache success path.
        let accepted = self.matches_parts_shared(kind, data, sender)?;
        PREDICATE_FRONT.with(|front| {
            front
                .borrow_mut()
                .insert(&self.cache, kind, data, sender, accepted)
        });
        Ok(accepted)
    }

    fn matches_parts_shared(
        &self,
        kind: &str,
        data: &str,
        sender: Option<&str>,
    ) -> Result<bool, Error> {
        if let Some(accepted) = self.cache.lookup(kind, data, sender)? {
            return Ok(accepted);
        }
        let _miss = self.cache.miss.lock().map_err(|_| {
            Error::new(
                ErrorKind::Transport,
                "Python predicate evaluation lock poisoned",
            )
        })?;
        if let Some(accepted) = self.cache.lookup(kind, data, sender)? {
            return Ok(accepted);
        }
        bounded(data)?;
        parse(data)?;
        let extra = format!(
            "\"kind\":{},\"data\":{},\"sender\":{}",
            quote(kind),
            quote(data),
            sender.map_or_else(|| "null".to_owned(), quote)
        );
        let (_worker, result) = self.module.history_request(
            self.state,
            "predicate",
            &extra,
            self.module.lock_worker()?,
        )?;
        let accepted = json_bool(result.field("accepted")?)?;
        let mut results = self.cache.results.write().map_err(|_| {
            Error::new(ErrorKind::Transport, "Python predicate cache lock poisoned")
        })?;
        let index = predicate_query_index(&results, kind, data, sender).unwrap_err();
        results.insert(
            index,
            (
                (Message::new(kind, data), sender.map(str::to_owned)),
                accepted,
            ),
        );
        Ok(accepted)
    }
}

fn json_bool(value: &Json) -> Result<bool, Error> {
    match value {
        Json::Bool(value) => Ok(*value),
        _ => Err(Error::new(ErrorKind::Transport, "expected worker boolean")),
    }
}

fn encode_json(value: &Json) -> String {
    match value {
        Json::Null => "null".to_owned(),
        Json::Bool(value) => value.to_string(),
        Json::Number(value) => value.clone(),
        Json::String(value) => quote(value),
        Json::Array(values) => format!(
            "[{}]",
            values.iter().map(encode_json).collect::<Vec<_>>().join(",")
        ),
        Json::Object(values) => format!(
            "{{{}}}",
            values
                .iter()
                .map(|(key, value)| { format!("{}:{}", quote(key), encode_json(value)) })
                .collect::<Vec<_>>()
                .join(",")
        ),
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
fn semantic_key(result: &Json) -> Result<Option<&str>, Error> {
    match result.field("semantic_key")? {
        Json::Null => Ok(None),
        value => value.string().map(Some),
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
    index: usize,
    states: BTreeMap<usize, usize>,
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
            .arg(options.semantic_state_cache.to_string())
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
            index: 0,
            states: BTreeMap::new(),
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

#[cfg(test)]
mod predicate_front_tests {
    use super::*;

    #[test]
    fn predicate_front_compares_identity_sender_and_every_query_field() {
        let first = Arc::new(PredicateCache::default());
        let second = Arc::new(PredicateCache::default());
        let mut front = PredicateFront::default();
        front.insert(&first, "DATA", "{}", Some("0"), true);
        assert_eq!(front.lookup(&first, "DATA", "{}", Some("0")), Some(true));
        assert_eq!(front.lookup(&second, "DATA", "{}", Some("0")), None);
        assert_eq!(front.lookup(&first, "ACK", "{}", Some("0")), None);
        assert_eq!(front.lookup(&first, "DATA", "[]", Some("0")), None);
        assert_eq!(front.lookup(&first, "DATA", "{}", Some("1")), None);
        assert_eq!(front.lookup(&first, "DATA", "{}", None), None);
        front.insert(&first, "DATA", "{}", Some("1"), false);
        front.insert(&first, "DATA", "{}", None, false);
        assert_eq!(front.lookup(&first, "DATA", "{}", Some("1")), Some(false));
        assert_eq!(front.lookup(&first, "DATA", "{}", None), Some(false));
    }

    #[test]
    fn predicate_front_bounds_queries_bytes_and_replaces_colliding_owners() {
        let first = Arc::new(PredicateCache::default());
        let mut front = PredicateFront::default();
        for query in 0..=PREDICATE_FRONT_QUERIES {
            front.insert(&first, "DATA", &query.to_string(), None, true);
        }
        let slot = PredicateFront::slot(&first);
        assert_eq!(front.slots[slot].results.len(), 1);
        assert_eq!(front.lookup(&first, "DATA", "0", None), None);
        let oversized = "x".repeat(PREDICATE_FRONT_BYTES + 1);
        front.insert(&first, "DATA", &oversized, None, true);
        assert_eq!(front.lookup(&first, "DATA", &oversized, None), None);
        for _ in 0..4 {
            let data = format!(
                "{}{}",
                front.slots[slot].bytes,
                "x".repeat(PREDICATE_FRONT_BYTES / 2)
            );
            front.insert(&first, "DATA", &data, None, false);
            assert!(front.slots[slot].bytes <= PREDICATE_FRONT_BYTES);
            assert!(front.slots[slot].results.len() <= PREDICATE_FRONT_QUERIES);
        }
        // The weak owner prevents address reuse but does not retain the cache.
        let address = Arc::as_ptr(&first);
        let weak = Arc::downgrade(&first);
        drop(first);
        assert!(weak.upgrade().is_none());
        assert_eq!(front.slots[slot].owner.as_ref().unwrap().as_ptr(), address);
        let mut candidates = Vec::new();
        let replacement = loop {
            let candidate = Arc::new(PredicateCache::default());
            if PredicateFront::slot(&candidate) == slot {
                break candidate;
            }
            candidates.push(candidate);
            assert!(
                candidates.len() < 100_000,
                "allocator never filled this slot"
            );
        };
        front.insert(&replacement, "DATA", "0", None, false);
        assert!(weak.upgrade().is_none());
        assert_eq!(front.lookup(&replacement, "DATA", "0", None), Some(false));
        assert_eq!(front.slots[slot].results.len(), 1);
    }

    #[test]
    #[ignore = "shared lock versus TLS predicate-front contention benchmark"]
    fn predicate_front_contention() {
        let owner = Arc::new(PredicateCache::default());
        owner
            .results
            .write()
            .unwrap()
            .push(((Message::new("DATA", "{}"), Some("0".to_owned())), true));
        for threads in [1, 12] {
            for front_enabled in [false, true] {
                let barrier = std::sync::Barrier::new(threads);
                let started = std::time::Instant::now();
                std::thread::scope(|scope| {
                    for _ in 0..threads {
                        let owner = &owner;
                        let barrier = &barrier;
                        scope.spawn(move || {
                            PREDICATE_FRONT.with(|front| {
                                front
                                    .borrow_mut()
                                    .insert(owner, "DATA", "{}", Some("0"), true)
                            });
                            barrier.wait();
                            for _ in 0..250_000 {
                                let accepted = if front_enabled {
                                    PREDICATE_FRONT.with(|front| {
                                        front.borrow().lookup(owner, "DATA", "{}", Some("0"))
                                    })
                                } else {
                                    owner.lookup("DATA", "{}", Some("0")).unwrap()
                                };
                                assert!(std::hint::black_box(accepted).unwrap());
                            }
                        });
                    }
                });
                eprintln!("predicate front: enabled={front_enabled}, threads={threads}, queries={}, elapsed={:?}", threads * 250_000, started.elapsed());
            }
        }
    }
}
