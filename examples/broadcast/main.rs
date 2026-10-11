use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use clap::Parser;

mod proc;
mod python;
#[cfg(test)]
mod solutions;
mod tests;

#[cfg(not(feature = "system-allocator"))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> std::process::ExitCode {
    if cfg!(target_os = "linux") && !cfg!(feature = "system-allocator") {
        // SAFETY: set mimalloc's process-wide option before exploration starts.
        unsafe {
            libmimalloc_sys::mi_option_set_enabled(libmimalloc_sys::mi_option_large_os_pages, true);
        }
    }
    run()
}

#[derive(Parser)]
#[command(about = "Check a Python broadcast solution")]
struct Args {
    solution: PathBuf,
}

fn run() -> ExitCode {
    match check(Args::parse()) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(2)
        }
    }
}

fn check(args: Args) -> Result<bool, String> {
    let path = args.solution;
    let module = must_python::PythonModule::new(
        &path,
        "BroadcastProcess",
        must_python::PythonOptions {
            max_states: usize::MAX,
            workers: tests::common::WORKERS,
            ..must_python::PythonOptions::default()
        },
    )
    .map_err(|error| format!("cannot load Python solution: {error}"))?;
    let diagnostics = python::Diagnostics::default();
    let factory = python::factory(module, diagnostics.clone());
    let started = Instant::now();
    let mut verdict = "pass";
    for (name, scenario) in tests::SCENARIOS {
        diagnostics.clear();
        let started = Instant::now();
        let result = scenario(factory.clone());
        let seconds = started.elapsed().as_secs_f64();
        let (status, detail) = match (diagnostics.get(), result) {
            (Some(error), _) => (error.status, error.message),
            (None, Ok(())) => ("pass", String::new()),
            (None, Err(error)) => {
                let status = if error.contains("send budget exceeded:") {
                    "send_budget"
                } else if error.contains("check incomplete:") {
                    "inconclusive"
                } else {
                    "fail"
                };
                (status, error)
            }
        };
        if matches!(status, "fail" | "send_budget") {
            verdict = "fail";
        } else if status != "pass" && verdict == "pass" {
            verdict = "inconclusive";
        }
        println!("{name:<18} {seconds:>8.3}s  {status}");
        if !detail.is_empty() {
            println!("{detail}");
        }
    }
    println!(
        "{} ({:.3}s)",
        verdict.to_uppercase(),
        started.elapsed().as_secs_f64()
    );
    Ok(verdict == "pass")
}
