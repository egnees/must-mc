//! String interning for message payloads.
//!
//! [`Val`](crate::event::Val) is a [`Sym`]: a 4-byte `Copy` handle for a payload string.
//! Interned so payloads compare and copy as a small integer.
//!
//! ## Determinism
//!
//! Ids are assigned by first-appearance order, so a given string's *id value* depends on
//! the (parallel) interleaving of interning. Nothing that affects the set or count of
//! explored executions may depend on the id *value* — only on id *equality* (two `Sym`s
//! are equal iff their strings are) and on the *resolved string*. `Sym` deliberately does
//! not implement `Ord`: any canonical ordering (the nondet option-set sort, the `min(S)`
//! canonicity test, the dedup key) must order by the resolved string via [`resolve`],
//! never by id. Enforced at compile time — sorting `Sym`s by id does not type-check.
//!
//! ## Parallelism
//!
//! The global table is the single source of truth for id assignment, so every worker maps
//! a string to the same id. Each worker also holds a thread-local, append-only cache for
//! both directions; the global lock is taken only the first time *this thread* sees a
//! given string (interning) or id (resolving), keeping the warm path lock-free.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// An interned payload: a small `Copy` handle for a string. Equal iff the strings are
/// equal. Intentionally not `Ord` — see the module docs on determinism.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sym(u32);

/// Global source of truth for id assignment. Strings are leaked (`&'static str`): payloads
/// live for the whole process, so `resolve` returns a `&'static str` with no lifetime
/// plumbing.
struct Global {
    fwd: HashMap<&'static str, u32>,
    strs: Vec<&'static str>,
    fingerprints: Vec<u64>,
}

static GLOBAL: OnceLock<Mutex<Global>> = OnceLock::new();

fn global() -> &'static Mutex<Global> {
    GLOBAL.get_or_init(|| {
        Mutex::new(Global {
            fwd: HashMap::new(),
            strs: Vec::new(),
            fingerprints: Vec::new(),
        })
    })
}

thread_local! {
    static LOCAL: RefCell<Local> = RefCell::new(Local::default());
}

/// Per-worker append-only caches: `fwd` for `intern` (string → sym), `strs` for `resolve`
/// (sym → string). Both only grow, and only when this thread meets a new string/id.
#[derive(Default)]
struct Local {
    fwd: HashMap<String, Sym>,
    strs: Vec<&'static str>,
    fingerprints: Vec<u64>,
}

/// Intern `s`, returning its stable [`Sym`]. Thread-local on the warm path (no lock, no
/// allocation); the global lock is taken only when *this thread* first sees `s`.
pub fn intern(s: &str) -> Sym {
    LOCAL.with(|l| {
        if let Some(&sym) = l.borrow().fwd.get(s) {
            return sym;
        }
        // First time on this thread: consult the global table (extending it if globally
        // new), then cache the answer locally so `s` never locks again.
        let sym = {
            let mut g = global().lock().unwrap();
            match g.fwd.get(s) {
                Some(&id) => Sym(id),
                None => {
                    let leaked: &'static str = Box::leak(s.to_owned().into_boxed_str());
                    let id = g.strs.len() as u32;
                    g.strs.push(leaked);
                    g.fingerprints.push(content_fingerprint(leaked));
                    g.fwd.insert(leaked, id);
                    Sym(id)
                }
            }
        };
        let mut l = l.borrow_mut();
        l.fwd.insert(s.to_owned(), sym);
        if l.strs.len() <= sym.0 as usize {
            refresh(&mut l);
        }
        sym
    })
}

/// Resolve `sym` to its payload string. Thread-local on the warm path.
pub fn resolve(sym: Sym) -> &'static str {
    LOCAL.with(|l| {
        if let Some(&s) = l.borrow().strs.get(sym.0 as usize) {
            return s;
        }
        let mut l = l.borrow_mut();
        refresh(&mut l);
        l.strs[sym.0 as usize]
    })
}

/// Extend both thread-local arrays to match the append-only global table.
fn refresh(local: &mut Local) {
    let g = global().lock().unwrap();
    if local.strs.len() < g.strs.len() {
        let old_len = local.strs.len();
        local.strs.extend_from_slice(&g.strs[old_len..]);
        local
            .fingerprints
            .extend_from_slice(&g.fingerprints[old_len..]);
    }
}

fn content_fingerprint(value: &str) -> u64 {
    value.bytes().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3)
    })
}

/// Deterministic payload hash for bounded memo lookup, never an equality or
/// ordering key. Callers must compare the actual symbols after a hash match.
pub(crate) fn fingerprint(sym: Sym) -> u64 {
    LOCAL.with(|local| {
        if let Some(&hash) = local.borrow().fingerprints.get(sym.0 as usize) {
            return hash;
        }
        let mut local = local.borrow_mut();
        refresh(&mut local);
        local.fingerprints[sym.0 as usize]
    })
}

impl From<&str> for Sym {
    fn from(s: &str) -> Self {
        intern(s)
    }
}

impl From<String> for Sym {
    fn from(s: String) -> Self {
        intern(&s)
    }
}

impl From<&String> for Sym {
    fn from(s: &String) -> Self {
        intern(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fingerprints_match_payload_bytes_across_thread_local_refreshes() {
        let first = intern("fingerprint:α\0payload");
        assert_eq!(fingerprint(first), content_fingerprint(resolve(first)));
        let (second, expected) = std::thread::spawn(move || {
            // A worker can receive an existing symbol before interning it.
            assert_eq!(fingerprint(first), content_fingerprint(resolve(first)));
            let second = intern("fingerprint:new payload");
            assert_eq!(fingerprint(second), content_fingerprint(resolve(second)));
            (second, fingerprint(second))
        })
        .join()
        .unwrap();
        assert_eq!(fingerprint(second), expected);
        assert_eq!(fingerprint(second), content_fingerprint(resolve(second)));
    }

    #[test]
    fn same_string_same_sym_roundtrips() {
        let a = intern("RV:2:1");
        let b = intern("RV:2:1");
        let c = intern("HB:1:0");
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(resolve(a), "RV:2:1");
        assert_eq!(resolve(c), "HB:1:0");
    }

    #[test]
    fn from_str_and_string_agree() {
        let a: Sym = "vote".into();
        let b: Sym = String::from("vote").into();
        assert_eq!(a, b);
        assert_eq!(resolve(a), "vote");
    }
}
