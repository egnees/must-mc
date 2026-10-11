#!/usr/bin/env python3
"""Run the broadcast checker against a directory of AnySystem submissions."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import threading
import time


ROOT = Path(__file__).resolve().parent.parent
STATUSES = ("pass", "fail", "unsupported", "inconclusive", "error", "send_budget", "timeout")
TESTS = ("concurrent", "reply", "reverse_reply", "sequential", "after_delivery")
MAX_LOG_BYTES = 2 * 1024 * 1024


def discover_submissions(directory):
    directory = Path(directory).resolve()
    if (directory / "04-broadcast").is_dir():
        directory /= "04-broadcast"
    if not directory.is_dir():
        raise ValueError(f"submission directory does not exist: {directory}")
    submissions = sorted(directory.rglob("broadcast.py"))
    if not submissions:
        raise ValueError(f"no broadcast.py submissions found in {directory}")
    return directory, submissions


def prioritize_submissions(submissions, first):
    first = first or []
    if len(first) != len(set(first)):
        raise ValueError("duplicate --first-submission names")
    missing = set(first) - submissions.keys()
    if missing:
        raise ValueError("unknown priority submissions: " + ", ".join(sorted(missing)))
    order = first + sorted(set(submissions) - set(first))
    return {name: submissions[name] for name in order}


def kill_group(process):
    """Also stop descendants when the group leader has already exited."""
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        elif process.poll() is None:
            process.kill()
    except ProcessLookupError:
        pass
    process.wait()


def read_capture(stream):
    stream.seek(0)
    data = stream.read(MAX_LOG_BYTES + 1)
    truncated = len(data) > MAX_LOG_BYTES
    text = data[:MAX_LOG_BYTES].decode("utf-8", errors="replace")
    if truncated:
        text += "\n[output truncated after 2 MiB]\n"
    return text, truncated


def run_process(command, timeout, stopped):
    """Capture bounded output while enforcing timeout on the full process group."""
    started = time.monotonic()
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        process = subprocess.Popen(
            command, stdout=stdout, stderr=stderr, start_new_session=os.name == "posix"
        )
        reason = None
        try:
            while process.poll() is None:
                if stopped.is_set():
                    reason = "interrupted"
                    break
                if any(os.fstat(stream.fileno()).st_size > MAX_LOG_BYTES
                       for stream in (stdout, stderr)):
                    reason = "output-limit"
                    break
                remaining = timeout - (time.monotonic() - started)
                if remaining <= 0:
                    reason = "timeout"
                    break
                try:
                    process.wait(timeout=min(remaining, 0.1))
                except subprocess.TimeoutExpired:
                    pass
        finally:
            kill_group(process)
        out, out_truncated = read_capture(stdout)
        err, err_truncated = read_capture(stderr)
        if reason is None and (out_truncated or err_truncated):
            reason = "output-limit"
    return {
        "returncode": process.returncode,
        "wall_seconds": time.monotonic() - started,
        "reason": reason,
        "stdout": out,
        "stderr": err,
        "output_truncated": out_truncated or err_truncated,
    }


def submission_command(args, solution):
    return [str(args.binary), str(solution)]


def parse_results(output, returncode, *, partial=False):
    results = {}
    current = None
    for line in output.splitlines():
        match = re.fullmatch(r"(\w+)\s+(\d+\.\d+)s\s+(\w+)", line)
        if match:
            name, seconds, status = match.groups()
            if name not in TESTS or name in results or status not in STATUSES[:-1]:
                raise ValueError(f"unexpected test result: {line}")
            current = {"test": name, "status": status, "seconds": float(seconds), "detail": ""}
            results[name] = current
        elif re.fullmatch(r"[A-Z_]+ \(\d+\.\d+s\)", line):
            current = None
        elif current is not None:
            current["detail"] += ("\n" if current["detail"] else "") + line
    missing = set(TESTS) - results.keys()
    if missing and not partial:
        raise ValueError("missing results: " + ", ".join(sorted(missing)))
    if not partial and all(item["status"] == "pass" for item in results.values()) and returncode != 0:
        raise ValueError("checker reported pass but exited unsuccessfully")
    return results


def run_submission(args, solution, submission, log_path, stopped):
    command = submission_command(args, solution)
    try:
        result = run_process(command, args.timeout, stopped)
    except OSError as error:
        result = {
            "returncode": None, "wall_seconds": 0.0, "reason": None,
            "stdout": "", "stderr": str(error), "output_truncated": False,
        }
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(
        "command: " + json.dumps(command, ensure_ascii=False)
        + "\n\n--- stdout ---\n" + result["stdout"]
        + "\n--- stderr ---\n" + result["stderr"], encoding="utf-8",
    )
    fallback = None
    parsed = {}
    if result["reason"]:
        status, detail = {
            "timeout": ("timeout", f"wall-clock limit exceeded ({args.timeout:g}s)"),
            "interrupted": ("inconclusive", "batch interrupted"),
            "output-limit": ("error", "checker output exceeded 2 MiB per stream"),
        }[result["reason"]]
        fallback = {"status": status, "seconds": None, "detail": detail}
        try:
            parsed = parse_results(result["stdout"], result["returncode"], partial=True)
        except ValueError:
            pass
    else:
        try:
            parsed = parse_results(result["stdout"], result["returncode"])
        except ValueError as error:
            detail = f"invalid checker result: {error}"
            if result["stderr"]:
                detail += "; " + result["stderr"].strip()[-2000:]
            fallback = {"status": "error", "seconds": None, "detail": detail}
    records = []
    for test in TESTS:
        record = {
            "submission": submission, "solution": str(solution), "test": test,
            "log": str(log_path), "command": command,
        }
        record.update({key: result[key] for key in (
            "returncode", "wall_seconds", "output_truncated"
        )})
        record.update(parsed.get(test, fallback))
        records.append(record)
    return records


def make_summary(records, submissions, tests, options, interrupted=False):
    records = sorted(records, key=lambda item: (item["submission"], item["test"]))
    totals = dict.fromkeys(STATUSES, 0)
    grouped = {}
    for name in sorted(submissions):
        cases = [record for record in records if record["submission"] == name]
        counts = dict.fromkeys(STATUSES, 0)
        for case in cases:
            counts[case["status"]] += 1
            totals[case["status"]] += 1
        passed = len(cases) == len(tests) and counts["pass"] == len(tests)
        grouped[name] = {"passed": passed, "completed": len(cases) == len(tests), "counts": counts, "results": cases}
    expected = len(submissions) * len(tests)
    return {
        "options": options, "tests": sorted(tests), "interrupted": interrupted,
        "expected_cases": expected, "completed_cases": len(records),
        "pending_cases": expected - len(records), "completed": len(records) == expected and not interrupted,
        "submission_order": list(submissions),
        "completed_submissions": sum(item["completed"] for item in grouped.values()),
        "counts": totals, "passed_submissions": sum(item["passed"] for item in grouped.values()),
        "total_submissions": len(submissions), "submissions": grouped,
    }


def write_summary(path, summary):
    """Replace one complete JSON snapshot; readers never observe half a write."""
    path = Path(path)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix=".summary-", suffix=".tmp", delete=False) as output:
            temporary = Path(output.name)
            json.dump(summary, output, ensure_ascii=False, sort_keys=True, indent=2)
            output.write("\n")
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def positive_int(value):
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def positive_float(value):
    parsed = float(value)
    if not 0 < parsed < float("inf"):
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return parsed


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("directory", nargs="?", type=Path,
                        default=ROOT.parent / "submissions-2025" / "04-broadcast")
    result.add_argument("--binary", type=Path, default=ROOT / "target/release/examples/broadcast")
    result.add_argument("--output", type=Path, default=ROOT / "target/broadcast-submissions")
    result.add_argument("--submission", action="append", help="exact relative submission folder; repeatable")
    result.add_argument("--first-submission", action="append", help="run this exact relative folder first without filtering the corpus; repeatable")
    result.add_argument("--timeout", type=positive_float, default=90.0)
    result.add_argument("--jobs", type=positive_int, default=1)
    return result


def main(argv=None):
    argument_parser = parser()
    args = argument_parser.parse_args(argv)
    args.binary = args.binary.resolve()
    args.output = args.output.resolve()
    stopped = threading.Event()
    try:
        directory, paths = discover_submissions(args.directory)
        submissions = {str(path.parent.relative_to(directory)): path for path in paths}
        if args.submission:
            missing = set(args.submission) - submissions.keys()
            if missing:
                raise ValueError("unknown submissions: " + ", ".join(sorted(missing)))
            submissions = {name: path for name, path in submissions.items() if name in args.submission}
        submissions = prioritize_submissions(submissions, args.first_submission)
        tests = TESTS
    except (OSError, ValueError) as error:
        argument_parser.error(str(error))
    args.output.mkdir(parents=True, exist_ok=True)
    options = {key: str(value) if isinstance(value, Path) else value for key, value in vars(args).items()}
    records = []
    summary_path = args.output / "summary.json"
    write_summary(summary_path, make_summary(records, submissions, tests, options))
    interrupted = False
    executor = ThreadPoolExecutor(max_workers=args.jobs)
    futures = {}
    print(f"Checking {len(submissions)} submissions × {len(tests)} tests ({args.jobs} jobs)", flush=True)
    try:
        with (args.output / "results.jsonl").open("w", encoding="utf-8") as output:
            for submission, path in submissions.items():
                log_path = args.output / "logs" / submission / "checker.log"
                future = executor.submit(run_submission, args, path, submission, log_path, stopped)
                futures[future] = submission
            try:
                completed = futures if args.jobs == 1 else as_completed(futures)
                for index, future in enumerate(completed, 1):
                    cases = future.result()
                    records.extend(cases)
                    for record in cases:
                        output.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
                    output.flush()
                    write_summary(summary_path, make_summary(records, submissions, tests, options))
                    counts = {status: sum(item["status"] == status for item in cases) for status in STATUSES}
                    details = ", ".join(f"{status}={count}" for status, count in counts.items() if count)
                    print(f"[{index}/{len(futures)}] {cases[0]['submission']}: {details}; "
                          f"{cases[0]['wall_seconds']:.3f}s", flush=True)
            except KeyboardInterrupt:
                interrupted = True
                stopped.set()
                for future in futures:
                    future.cancel()
                executor.shutdown(wait=True, cancel_futures=True)
                recorded = {record["submission"] for record in records}
                for future, submission in futures.items():
                    if future.cancelled() or submission in recorded:
                        continue
                    cases = future.result()
                    records.extend(cases)
                    for record in cases:
                        output.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
                    output.flush()
    finally:
        stopped.set()
        executor.shutdown(wait=True, cancel_futures=True)
    summary = make_summary(records, submissions, tests, options, interrupted)
    write_summary(summary_path, summary)
    counts = ", ".join(f"{key}={value}" for key, value in summary["counts"].items() if value)
    print(f"Passed submissions: {summary['passed_submissions']}/{len(submissions)}; {counts}")
    print(f"Reports: {args.output}")
    return 130 if interrupted else int(summary["passed_submissions"] != len(submissions))


if __name__ == "__main__":
    sys.exit(main())
