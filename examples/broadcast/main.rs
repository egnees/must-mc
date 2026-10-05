//! Rust: cargo run --release --example broadcast -- causal
//! Python: cargo run --release --example broadcast -- --python path/to/broadcast.py

use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use clap::Parser;
use proc::Factory;

mod proc;
mod python;
mod solutions;
mod tests;

#[cfg(not(feature = "system-allocator"))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn enable_hugepages() {
    if cfg!(target_os = "linux") && !cfg!(feature = "system-allocator") {
        // SAFETY: mimalloc's thread-safe option API, called once before exploration.
        unsafe {
            libmimalloc_sys::mi_option_set_enabled(libmimalloc_sys::mi_option_large_os_pages, true);
        }
    }
}

type Test = fn(Factory) -> Result<usize, String>;
const TESTS: [(&str, Test); 10] = [
    ("liveness/concurrent", tests::liveness::concurrent::run),
    ("liveness/reply", tests::liveness::reply::run),
    (
        "liveness/reverse_reply",
        tests::liveness::reverse_reply::run,
    ),
    ("liveness/sequential", tests::liveness::sequential::run),
    (
        "liveness/after_delivery",
        tests::liveness::after_delivery::run,
    ),
    ("safety/concurrent", tests::safety::concurrent::run),
    ("safety/reply", tests::safety::reply::run),
    ("safety/reverse_reply", tests::safety::reverse_reply::run),
    ("safety/sequential", tests::safety::sequential::run),
    ("safety/after_delivery", tests::safety::after_delivery::run),
];
#[derive(Parser)]
#[command(about = "Check a Rust or AnySystem Python broadcast process")]
struct Args {
    #[arg(conflicts_with = "python")]
    solution: Option<String>,
    #[arg(long)]
    python: Option<PathBuf>,
    #[arg(long, default_value = "BroadcastProcess")]
    class: String,
    #[arg(long, default_value = "python3")]
    interpreter: PathBuf,
    #[arg(long)]
    test: Option<String>,
    #[arg(long)]
    list_tests: bool,
    #[arg(long)]
    json: bool,
    #[arg(long, default_value_t = 12)]
    threads: usize,
    #[arg(long, default_value_t = 16)]
    max_sends: usize,
    #[arg(long, default_value_t = 5000)]
    python_timeout_ms: u64,
    #[arg(long, default_value_t = 100000)]
    python_max_states: usize,
    #[arg(long, default_value_t = 0)]
    seed: u64,
}

fn main() -> std::process::ExitCode {
    enable_hugepages();
    let args = Args::parse();
    if args.list_tests {
        for (name, _) in TESTS {
            println!("{name}");
        }
        return std::process::ExitCode::SUCCESS;
    }
    if args
        .test
        .as_ref()
        .is_some_and(|name| !TESTS.iter().any(|(known, _)| name == known))
    {
        eprintln!("unknown test: {}", args.test.as_deref().unwrap());
        return std::process::ExitCode::from(2);
    }
    tests::common::configure(args.threads, args.max_sends);
    let diagnostics = python::Diagnostics::default();
    let (name, factory): (String, Factory) = if let Some(path) = &args.python {
        let options = must_python::PythonOptions {
            python: args.interpreter,
            timeout: Duration::from_millis(args.python_timeout_ms),
            max_states: args.python_max_states,
            seed: args.seed,
        };
        let module = match must_python::PythonModule::new(path, &args.class, options) {
            Ok(module) => module,
            Err(error) => {
                eprintln!("cannot load Python solution: {error}");
                return std::process::ExitCode::from(2);
            }
        };
        (
            path.display().to_string(),
            python::factory(module, diagnostics.clone()),
        )
    } else {
        let name = args.solution.as_deref().unwrap_or("causal");
        let factory: Factory = match name {
            "causal" => Arc::new(solutions::causal::new),
            "direct" => Arc::new(solutions::direct::new),
            "early_gc" => Arc::new(solutions::early_gc::new),
            "flood" => Arc::new(solutions::flood::new),
            "last_dependency" => Arc::new(solutions::last_dependency::new),
            "send_then_deliver" => Arc::new(solutions::send_then_deliver::new),
            "majority_ack" => Arc::new(solutions::majority_ack::new),
            "outbox_sequence" => Arc::new(solutions::outbox_sequence::new),
            "prefix_clock" => Arc::new(solutions::prefix_clock::new),
            _ => {
                eprintln!("unknown solution: {name}");
                return std::process::ExitCode::from(2);
            }
        };
        (name.to_owned(), factory)
    };
    if !args.json {
        println!(
            "{name}: {} threads, send limit {}",
            tests::common::threads(),
            args.max_sends
        );
    }
    let started = Instant::now();
    let mut passed = 0;
    let mut total = 0;
    let mut failures = Vec::new();
    for (test, run) in TESTS {
        if args.test.as_ref().is_some_and(|name| name != test) {
            continue;
        }
        diagnostics.clear();
        let test_started = Instant::now();
        let result = run(factory.clone());
        let seconds = test_started.elapsed().as_secs_f64();
        let diagnostic = diagnostics.get();
        let (status, events, detail) = match (diagnostic, result) {
            (Some(error), result) => (
                error.status,
                None,
                format!("{}\n{}", error.message, result.err().unwrap_or_default()),
            ),
            (None, Ok(events)) => ("pass", Some(events), String::new()),
            (None, Err(error)) if error.contains("check incomplete:") => {
                ("inconclusive", None, error)
            }
            (None, Err(error)) => ("fail", None, error),
        };
        total += 1;
        if status == "pass" {
            passed += 1;
        }
        if args.json {
            println!("{{\"solution\":{},\"test\":{},\"status\":{},\"seconds\":{seconds:.6},\"events\":{},\"detail\":{}}}",
                json_string(&name), json_string(test), json_string(status),
                events.map_or_else(|| "null".into(), |value| value.to_string()), json_string(&detail));
        } else {
            println!(
                "{test:<24} {status:<12} {seconds:>8.3}s  {} events",
                events.unwrap_or(0)
            );
            if status != "pass" {
                failures.push((test, detail));
            }
        }
    }
    if !args.json {
        println!(
            "total: {:.3}s, passed: {passed}/{total}",
            started.elapsed().as_secs_f64()
        );
        for (test, detail) in failures {
            println!("\n{test}:\n{detail}");
        }
    }
    if passed == total {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::FAILURE
    }
}

pub(crate) fn json_string(value: &str) -> String {
    use std::fmt::Write;
    let mut result = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '\x00'..='\x1f' => {
                write!(result, "\\u{:04x}", ch as u32).unwrap();
            }
            _ => result.push(ch),
        }
    }
    result.push('"');
    result
}
