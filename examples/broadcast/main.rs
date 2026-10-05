//! Run all checks: cargo run --release --example broadcast -- causal

use std::time::Instant;

mod proc;
mod solutions;
mod tests;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

// Same best-effort large-page setting as raft_election; a no-op off Linux.
fn enable_hugepages() {
    if cfg!(target_os = "linux") {
        // SAFETY: mimalloc's thread-safe option API, called once before exploration.
        unsafe {
            libmimalloc_sys::mi_option_set_enabled(libmimalloc_sys::mi_option_large_os_pages, true);
        }
    }
}

type Factory = fn(usize, usize) -> Box<dyn proc::Process>;
type Test = fn(Factory) -> Result<usize, String>;

fn main() -> std::process::ExitCode {
    enable_hugepages();
    let mut args = std::env::args().skip(1);
    let usage = "usage: cargo run --release --example broadcast -- <causal|direct|early_gc|flood|send_then_deliver|majority_ack|outbox_sequence|prefix_clock|last_dependency>";
    let Some(solution) = args.next() else {
        eprintln!("{usage}");
        return std::process::ExitCode::FAILURE;
    };
    if args.next().is_some() {
        eprintln!("{usage}");
        return std::process::ExitCode::FAILURE;
    }
    let factory: Factory = match solution.as_str() {
        "causal" => solutions::causal::new,
        "direct" => solutions::direct::new,
        "early_gc" => solutions::early_gc::new,
        "flood" => solutions::flood::new,
        "last_dependency" => solutions::last_dependency::new,
        "send_then_deliver" => solutions::send_then_deliver::new,
        "majority_ack" => solutions::majority_ack::new,
        "outbox_sequence" => solutions::outbox_sequence::new,
        "prefix_clock" => solutions::prefix_clock::new,
        _ => {
            eprintln!("unknown solution: {solution}\n{usage}");
            return std::process::ExitCode::FAILURE;
        }
    };
    let tests: [(&str, Test); 10] = [
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
    let profile = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    println!(
        "{solution}: {profile}, {} threads, mimalloc",
        tests::common::THREADS
    );
    let started = Instant::now();
    let mut failures = Vec::new();
    let mut liveness_seconds = 0.0;
    let mut safety_seconds = 0.0;
    for (name, run) in tests {
        let test_started = Instant::now();
        let result = run(factory);
        let seconds = test_started.elapsed().as_secs_f64();
        if name.starts_with("liveness/") {
            liveness_seconds += seconds;
        } else {
            safety_seconds += seconds;
        }
        match result {
            Ok(events) => println!("{name:<24} OK   {seconds:>8.3}s  {events} events"),
            Err(error) => {
                println!("{name:<24} FAIL {seconds:>8.3}s");
                failures.push((name, error));
            }
        }
    }
    println!("liveness: {liveness_seconds:.3}s, safety: {safety_seconds:.3}s");
    println!(
        "total: {:.3}s, passed: {}/{}",
        started.elapsed().as_secs_f64(),
        tests.len() - failures.len(),
        tests.len()
    );
    // Print bad executions after the timings, and keep running after failed tests.
    for (name, error) in &failures {
        println!("\n{name}:\n{error}");
    }
    if failures.is_empty() {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::FAILURE
    }
}
