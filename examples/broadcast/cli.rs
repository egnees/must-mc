use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use crate::{python, tests};
use clap::Parser;

#[derive(Parser)]
#[command(about = "Check a Python broadcast solution")]
struct Args {
    #[arg(required_unless_present = "list_tests")]
    solution: Option<PathBuf>,
    #[arg(long)]
    list_tests: bool,
    #[arg(long)]
    test: Option<String>,
    #[arg(long)]
    json: bool,
    #[arg(long, default_value_t = 12)]
    threads: usize,
}

pub(crate) fn run() -> ExitCode {
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
    if args.list_tests {
        for (name, _) in tests::SCENARIOS {
            println!("{name}");
        }
        return Ok(true);
    }
    if let Some(name) = &args.test {
        if !tests::SCENARIOS.iter().any(|(known, _)| known == name) {
            return Err(format!("unknown test: {name}"));
        }
    }
    let path = args.solution.expect("clap requires a solution path");
    let module = must_python::PythonModule::new(
        &path,
        "BroadcastProcess",
        must_python::PythonOptions {
            max_states: usize::MAX,
            workers: args.threads.max(1),
            ..must_python::PythonOptions::default()
        },
    )
    .map_err(|error| format!("cannot load Python solution: {error}"))?;
    tests::common::configure(args.threads);
    let diagnostics = python::Diagnostics::default();
    let factory = python::factory(module, diagnostics.clone());
    let started = Instant::now();
    let mut verdict = "pass";
    for (name, scenario) in tests::SCENARIOS {
        if args.test.as_ref().is_some_and(|test| test != name) {
            continue;
        }
        diagnostics.clear();
        let started = Instant::now();
        let result = scenario(factory.clone());
        let seconds = started.elapsed().as_secs_f64();
        let (status, detail, events) = match (diagnostics.get(), result) {
            (Some(error), _) => (error.status, error.message, None),
            (None, Ok(events)) => ("pass", String::new(), Some(events)),
            (None, Err(error)) => {
                let status = if error.contains("send budget exceeded:") {
                    "send_budget"
                } else if error.contains("check incomplete:") {
                    "inconclusive"
                } else {
                    "fail"
                };
                (status, error, None)
            }
        };
        if matches!(status, "fail" | "send_budget") {
            verdict = "fail";
        } else if status != "pass" && verdict == "pass" {
            verdict = "inconclusive";
        }
        if args.json {
            use python::json_string as quote;
            println!("{{\"solution\":{},\"test\":{},\"status\":{},\"seconds\":{seconds:.6},\"events\":{},\"detail\":{}}}",
                quote(&path.display().to_string()), quote(name), quote(status),
                events.map_or_else(|| "null".into(), |events| events.to_string()), quote(&detail));
        } else {
            println!("{name:<18} {seconds:>8.3}s  {status}");
            if !detail.is_empty() {
                println!("{detail}");
            }
        }
    }
    if !args.json {
        println!(
            "{} ({:.3}s)",
            verdict.to_uppercase(),
            started.elapsed().as_secs_f64()
        );
    }
    Ok(verdict == "pass")
}
