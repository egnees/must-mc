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
MAX_LOG_BYTES = 2 * 1024 * 1024


def anysystem_result(solution):
    directory = Path(solution).parent
    try:
        score = (directory / "score").read_text().strip()
    except OSError:
        score = "unknown"
    try:
        log = (directory / "log").read_text(errors="replace")
    except OSError:
        return f"score={score}; log unavailable"
    passed = re.search(r"Passed (\d+) from (\d+) tests", log)
    parts = [f"score={score}"]
    if passed:
        parts.append(f"tests={passed[1]}/{passed[2]}")
    for section in re.finditer(r"^--- ([^\n]+) ---\n(.*?)(?=^--- |\Z)", log,
                               re.MULTILINE | re.DOTALL):
        name, body = section.groups()
        if not name.startswith("MODEL CHECKING"):
            continue
        verdict = re.search(r"^(PASSED|FAILED)\b", body, re.MULTILINE)
        parts.append(f"{name}={verdict[1] if verdict else 'unknown'}")
    return "; ".join(parts)


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


def case_command(args, solution, test):
    return [str(args.binary), str(solution), "--test", test,
            "--threads", str(args.threads), "--json"]


def listing_command(args):
    return [str(args.binary), "--list-tests"]


def run_case(args, solution, submission, test, log_path, stopped):
    command = case_command(args, solution, test)
    record = {
        "submission": submission, "solution": str(solution), "test": test,
        "status": "error", "seconds": None, "events": None, "detail": "",
        "log": str(log_path), "command": command,
        "delivery": "asyn", "liveness_mode": "cuts",
    }
    try:
        result = run_process(command, args.timeout, stopped)
    except OSError as error:
        result = {
            "returncode": None, "wall_seconds": 0.0, "reason": None,
            "stdout": "", "stderr": str(error), "output_truncated": False,
        }
    record.update({key: result[key] for key in (
        "returncode", "wall_seconds", "output_truncated"
    )})
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(
        "command: " + json.dumps(command, ensure_ascii=False)
        + "\n\n--- stdout ---\n" + result["stdout"]
        + "\n--- stderr ---\n" + result["stderr"], encoding="utf-8",
    )
    if result["reason"]:
        record["status"], record["detail"] = {
            "timeout": ("timeout", f"wall-clock limit exceeded ({args.timeout:g}s)"),
            "interrupted": ("inconclusive", "batch interrupted"),
            "output-limit": ("error", "checker output exceeded 2 MiB per stream"),
        }[result["reason"]]
        return record
    try:
        response = json.loads(result["stdout"])
        if not isinstance(response, dict):
            raise ValueError("expected one JSON object")
        required = {"solution", "test", "status", "seconds", "events", "detail"}
        if not required.issubset(response):
            raise ValueError("missing result fields: " + ", ".join(sorted(required - response.keys())))
        if response["test"] != test:
            raise ValueError(f"unexpected test name: {response['test']!r}")
        if response["status"] not in STATUSES[:-1]:
            raise ValueError(f"unknown status: {response['status']!r}")
        if "delivery" in response and response["delivery"] != "asyn":
            raise ValueError(f"unexpected delivery model: {response['delivery']!r}")
        if "liveness_mode" in response and response["liveness_mode"] != "cuts":
            raise ValueError(f"unexpected liveness mode: {response['liveness_mode']!r}")
        if response["status"] == "pass" and result["returncode"] != 0:
            raise ValueError("checker reported pass but exited unsuccessfully")
        record.update({key: response[key] for key in ("status", "seconds", "events", "detail")})
        record["checker_solution"] = response["solution"]
    except (ValueError, TypeError) as error:
        record["detail"] = f"invalid checker result: {error}"
        if result["stderr"]:
            record["detail"] += "; " + result["stderr"].strip()[-2000:]
    return record


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
    result.add_argument("--test", action="append", help="exact checker test name; repeatable")
    result.add_argument("--timeout", type=positive_float, default=90.0)
    result.add_argument("--jobs", type=positive_int, default=1)
    result.add_argument("--threads", type=positive_int, default=12)
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
        listed = run_process(listing_command(args), args.timeout, stopped)
        if listed["returncode"] != 0 or listed["reason"]:
            raise ValueError("cannot list checker tests: " + (listed["stderr"].strip() or str(listed["reason"])))
        available = [line.strip() for line in listed["stdout"].splitlines() if line.strip()]
        if not available or len(available) != len(set(available)):
            raise ValueError("checker returned an empty or duplicate test list")
        tests = sorted(set(args.test or available))
        missing_tests = set(tests) - set(available)
        if missing_tests:
            raise ValueError("unknown tests: " + ", ".join(sorted(missing_tests)))
    except (OSError, ValueError) as error:
        argument_parser.error(str(error))
    args.output.mkdir(parents=True, exist_ok=True)
    options = {key: str(value) if isinstance(value, Path) else value for key, value in vars(args).items()}
    options.update(delivery="asyn", liveness_mode="cuts")
    records = []
    summary_path = args.output / "summary.json"
    write_summary(summary_path, make_summary(records, submissions, tests, options))
    finished = dict.fromkeys(submissions, 0)
    interrupted = False
    executor = ThreadPoolExecutor(max_workers=args.jobs)
    futures = {}
    print(f"Checking {len(submissions)} submissions × {len(tests)} tests ({args.jobs} jobs)", flush=True)
    try:
        with (args.output / "results.jsonl").open("w", encoding="utf-8") as output:
            for submission, path in submissions.items():
                for index, test in enumerate(tests):
                    log_path = args.output / "logs" / submission / f"{index:02d}.log"
                    future = executor.submit(run_case, args, path, submission, test, log_path, stopped)
                    futures[future] = (submission, test)
            try:
                completed = futures if args.jobs == 1 else as_completed(futures)
                for future in completed:
                    record = future.result()
                    records.append(record)
                    output.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
                    output.flush()
                    submission = record["submission"]
                    if finished[submission] == 0:
                        print(f"{submission}: AnySystem {anysystem_result(record['solution'])}", flush=True)
                    seconds = record["seconds"]
                    timing = (f"{seconds:.3f}s" if isinstance(seconds, (int, float))
                              else f"{record['wall_seconds']:.3f}s (wall)")
                    print(f"[{len(records)}/{len(futures)}] {submission} / {record['test']}: "
                          f"{record['status']} — {timing}; events={record['events']}", flush=True)
                    finished[submission] += 1
                    if finished[submission] == len(tests):
                        write_summary(summary_path, make_summary(records, submissions, tests, options))
                        cases = [item for item in records if item["submission"] == submission]
                        counts = {status: sum(item["status"] == status for item in cases) for status in STATUSES}
                        details = ", ".join(f"{status}={count}" for status, count in counts.items() if count)
                        print(f"{submission}: {details}", flush=True)
            except KeyboardInterrupt:
                interrupted = True
                stopped.set()
                for future in futures:
                    future.cancel()
                executor.shutdown(wait=True, cancel_futures=True)
                recorded = {(record["submission"], record["test"]) for record in records}
                for future, key in futures.items():
                    if future.cancelled() or key in recorded:
                        continue
                    record = future.result()
                    records.append(record)
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
