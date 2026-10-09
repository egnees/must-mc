"""Tests for the submission batch runner, using a fake checker executable."""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock


SPEC = importlib.util.spec_from_file_location(
    "broadcast_batch", Path(__file__).with_name("test_broadcast_submissions.py")
)
batch = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(batch)


FAKE_CHECKER = r'''
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

if "--list-tests" in sys.argv:
    print("concurrent\nreply\nreverse_reply\nsequential\nafter_delivery")
    sys.exit(0)
parser = argparse.ArgumentParser()
parser.add_argument("solution")
parser.add_argument("--test")
args, _ = parser.parse_known_args()
mode = Path(args.solution).read_text().strip()
if mode == "cwd":
    Path("working-directory.txt").write_text(str(Path.cwd()))
if mode == "missing":
    print("startup failed", file=sys.stderr)
    sys.exit(2)
if mode == "malformed":
    print("not-json")
    sys.exit(0)
if mode == "mismatch":
    args.test = "wrong-test"
if mode == "timeout":
    marker = str(Path(args.solution).with_suffix(".alive"))
    child = subprocess.Popen([sys.executable, "-c",
        "import pathlib,time; time.sleep(1); pathlib.Path(" + repr(marker)
        + ").write_text('survived'); time.sleep(60)"])
    Path(args.solution).with_suffix(".pid").write_text(str(child.pid))
    time.sleep(60)
if mode == "verbose":
    print("x" * (3 * 1024 * 1024))
    sys.exit(0)
if mode in ("flood-stdout", "flood-stderr"):
    stream = sys.stdout if mode == "flood-stdout" else sys.stderr
    while True:
        stream.write("x" * 65536)
        stream.flush()
        time.sleep(0.005)
status = mode if mode in ("fail", "unsupported", "inconclusive", "error", "send_budget") else "pass"
print(json.dumps({"solution": args.solution, "test": args.test, "status": status,
                  "seconds": 0.1, "events": 3, "detail": "fixture " + status,
                  "delivery": "p2p" if mode == "wrong-delivery" else "asyn",
                  "liveness_mode": "explicit" if mode == "wrong-mode" else "cuts"}))
sys.exit(1 if status != "pass" or mode == "badexit" else 0)
'''


class BatchTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.corpus = self.root / "submissions" / "04-broadcast"
        self.corpus.mkdir(parents=True)
        self.binary = self.root / "fake-checker"
        self.binary.write_text(f"#!{sys.executable}\n" + FAKE_CHECKER)
        self.binary.chmod(0o755)
        self.output = self.root / "reports"

    def solution(self, name, mode="pass"):
        path = self.corpus / name / "broadcast.py"
        path.parent.mkdir(parents=True)
        path.write_text(mode)
        return path

    def args(self, *extra):
        args = batch.parser().parse_args([
            str(self.corpus), "--binary", str(self.binary), "--output", str(self.output),
            "--timeout", "3", *extra,
        ])
        return args

    def case(self, name, mode, *extra):
        path = self.solution(name, mode)
        return batch.run_case(
            self.args(*extra), path, name, "concurrent",
            self.output / f"{name}.log", threading.Event(),
        )

    def test_discovery_accepts_parent_and_broadcast_directory(self):
        first = self.solution("a")
        last = self.solution("nested/z")
        for root in (self.corpus, self.corpus.parent):
            directory, paths = batch.discover_submissions(root)
            self.assertEqual(directory, self.corpus.resolve())
            self.assertEqual(paths, [first.resolve(), last.resolve()])

    def test_discovery_rejects_empty_directory(self):
        with self.assertRaisesRegex(ValueError, "no broadcast.py"):
            batch.discover_submissions(self.corpus)

    def test_priority_is_order_only_and_rejects_duplicate_or_unknown_names(self):
        submissions = {name: self.solution(name) for name in ("a", "z", "b", "m")}
        ordered = batch.prioritize_submissions(submissions, ["z", "m"])
        self.assertEqual(list(ordered), ["z", "m", "a", "b"])
        self.assertEqual(set(ordered), set(submissions))
        self.assertEqual(batch.prioritize_submissions(submissions, None),
                         {name: submissions[name] for name in sorted(submissions)})
        with self.assertRaisesRegex(ValueError, "duplicate"):
            batch.prioritize_submissions(submissions, ["z", "z"])
        with self.assertRaisesRegex(ValueError, "unknown priority"):
            batch.prioritize_submissions(submissions, ["absent"])

    def test_atomic_partial_summary_and_sequential_priority_batch(self):
        for name in ["a", "z", "b"]:
            self.solution(name)
        snapshots = []
        original = batch.write_summary

        def capture(path, summary):
            original(path, summary)
            snapshots.append(json.loads(Path(path).read_text()))

        with mock.patch.object(batch, "write_summary", side_effect=capture):
            with contextlib.redirect_stdout(io.StringIO()):
                code = batch.main([
                    str(self.corpus), "--binary", str(self.binary), "--output", str(self.output),
                    "--first-submission", "z", "--threads", "12",
                ])
        self.assertEqual(code, 0)
        self.assertEqual(snapshots[0]["completed_cases"], 0)
        self.assertEqual(snapshots[0]["pending_cases"], 15)
        partial = snapshots[1]
        self.assertEqual(partial["completed_submissions"], 1)
        self.assertTrue(partial["submissions"]["z"]["completed"])
        self.assertFalse(partial["submissions"]["a"]["completed"])
        self.assertFalse(partial["completed"])
        self.assertEqual(partial["pending_cases"], 10)
        self.assertTrue(snapshots[-1]["completed"])
        self.assertEqual(snapshots[-1]["pending_cases"], 0)
        records = [json.loads(line) for line in (self.output / "results.jsonl").read_text().splitlines()]
        self.assertEqual([record["submission"] for record in records], ["z"] * 5 + ["a"] * 5 + ["b"] * 5)
        for record in records:
            command = record["command"]
            self.assertEqual(command[command.index("--threads") + 1], "12")
            self.assertNotIn("--max-sends", command)
        self.assertEqual(list(self.output.glob(".summary-*.tmp")), [])

    def test_failed_atomic_replace_preserves_the_previous_summary(self):
        self.output.mkdir()
        summary = self.output / "summary.json"
        batch.write_summary(summary, {"generation": 1})
        with mock.patch.object(batch.os, "replace", side_effect=OSError("replacement failed")):
            with self.assertRaisesRegex(OSError, "replacement failed"):
                batch.write_summary(summary, {"generation": 2})
        self.assertEqual(json.loads(summary.read_text()), {"generation": 1})
        self.assertEqual(list(self.output.glob(".summary-*.tmp")), [])

    def test_send_budget_is_a_completed_failure_with_distinct_statistics(self):
        self.solution("over-budget", "send_budget")
        self.solution("semantic-error", "fail")
        progress = io.StringIO()
        with contextlib.redirect_stdout(progress):
            code = batch.main([
                str(self.corpus), "--binary", str(self.binary), "--output", str(self.output),
                "--test", "concurrent",
            ])
        self.assertEqual(code, 1)
        summary = json.loads((self.output / "summary.json").read_text())
        self.assertTrue(summary["completed"])
        self.assertEqual(summary["counts"]["send_budget"], 1)
        self.assertEqual(summary["counts"]["fail"], 1)
        self.assertEqual(summary["counts"]["timeout"], 0)
        self.assertEqual(summary["counts"]["inconclusive"], 0)
        self.assertEqual(summary["passed_submissions"], 0)
        over_budget = summary["submissions"]["over-budget"]
        self.assertTrue(over_budget["completed"])
        self.assertFalse(over_budget["passed"])
        self.assertEqual(over_budget["results"][0]["status"], "send_budget")
        self.assertIn("send_budget", progress.getvalue())

    @unittest.skipUnless(os.name == "posix", "launcher uses a POSIX shell")
    def test_launcher_freezes_checker_preserves_paths_and_forwards_night_bounds(self):
        repo = self.root / "repo with spaces"
        scripts = repo / "scripts"
        scripts.mkdir(parents=True)
        for name in ["run_broadcast_all.sh", "test_broadcast_submissions.py"]:
            shutil.copyfile(Path(__file__).with_name(name), scripts / name)
        binary = repo / "target/release/examples/broadcast"
        binary.parent.mkdir(parents=True)
        shutil.copyfile(self.binary, binary)
        priorities = ["artyukhov_dmitriy_a", "baydakov_kirill_a", "artemov_mikhail_s"]
        for name in priorities:
            self.solution(name, "cwd" if name == priorities[0] else "pass")
        self.solution("extra", "fail")
        commands = self.root / "fake commands"
        commands.mkdir()
        cargo = commands / "cargo"
        cargo.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > "$CARGO_CALLS"\n')
        cargo.chmod(0o755)
        caffeinate = commands / "caffeinate"
        caffeinate.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > "$SLEEP_ARGS"\n[ "$1" = "-i" ] || exit 2\nshift\nexec "$@"\n')
        caffeinate.chmod(0o755)
        cargo_calls = self.root / "cargo-arguments"
        sleep_args = self.root / "sleep-arguments"
        env = dict(os.environ, PATH=str(commands) + os.pathsep + os.environ["PATH"],
                   CARGO_CALLS=str(cargo_calls), SLEEP_ARGS=str(sleep_args), CARGO_TOOLCHAIN="fake-version")
        output = self.root / "night results with spaces"
        result = subprocess.run(["bash", str(scripts / "run_broadcast_all.sh"), str(self.corpus.parent), str(output)],
                                env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(cargo_calls.read_text().splitlines(), ["+fake-version", "build", "--release", "--example", "broadcast"])
        self.assertEqual((output / "broadcast").read_bytes(), binary.read_bytes())
        self.assertEqual(
            Path((output / "work/working-directory.txt").read_text()).resolve(),
            (output / "work").resolve(),
        )
        self.assertFalse((repo / "working-directory.txt").exists())
        self.assertEqual(sleep_args.read_text().splitlines()[0], "-i")
        summary = json.loads((output / "summary.json").read_text())
        self.assertTrue(summary["completed"])
        self.assertEqual(summary["total_submissions"], 4)
        self.assertEqual(summary["submission_order"], priorities + ["extra"])
        for option, value in [("jobs", 1), ("threads", 12), ("timeout", 90), ("delivery", "asyn"), ("liveness_mode", "cuts")]:
            self.assertEqual(summary["options"][option], value)

    def test_listing_and_explicit_test_selection(self):
        self.assertEqual(batch.listing_command(self.args()),
                         [str(self.binary), "--list-tests"])
        self.assertEqual(batch.listing_command(self.args("--test", "reply")),
                         [str(self.binary), "--list-tests"])
        self.solution("good")
        with contextlib.redirect_stdout(io.StringIO()):
            code = batch.main([
                str(self.corpus), "--binary", str(self.binary), "--output", str(self.output),
                "--test", "reply",
            ])
        self.assertEqual(code, 0)
        summary = json.loads((self.output / "summary.json").read_text())
        self.assertEqual(summary["expected_cases"], 1)
        self.assertEqual(summary["submissions"]["good"]["results"][0]["test"], "reply")

    def test_case_command_uses_positional_solution(self):
        command = batch.case_command(self.args(), self.corpus / "broadcast.py", "concurrent")
        self.assertNotIn("--max-sends", command)
        for option in ("--delivery", "--liveness-mode", "--suite"):
            self.assertNotIn(option, command)
        self.assertEqual(command[1], str(self.corpus / "broadcast.py"))
        self.assertNotIn("--python", command)

    def test_result_statuses_and_nonzero_expected_failure(self):
        for status in ("pass", "fail", "unsupported", "inconclusive", "error"):
            with self.subTest(status=status):
                result = self.case(status, status)
                self.assertEqual(result["status"], status)
                self.assertEqual(result["events"], 3)
                self.assertEqual(result["returncode"], 0 if status == "pass" else 1)
                self.assertIn("fixture " + status, Path(result["log"]).read_text())

    def test_invalid_results_are_errors_with_logs(self):
        for mode in ("missing", "malformed", "mismatch", "badexit", "wrong-delivery", "wrong-mode"):
            with self.subTest(mode=mode):
                result = self.case(mode, mode)
                self.assertEqual(result["status"], "error")
                self.assertIn("invalid checker result", result["detail"])
        result = self.case("startup", "missing")
        self.assertIn("startup failed", result["detail"])

    def test_output_is_bounded(self):
        result = self.case("verbose", "verbose")
        self.assertTrue(result["output_truncated"])
        self.assertLess(Path(result["log"]).stat().st_size, batch.MAX_LOG_BYTES + 4096)
        self.assertEqual(result["status"], "error")

    def test_continuous_output_is_stopped_before_timeout(self):
        for mode in ("flood-stdout", "flood-stderr"):
            with self.subTest(mode=mode):
                started = time.monotonic()
                result = self.case(mode, mode, "--timeout", "30")
                self.assertLess(time.monotonic() - started, 3)
                self.assertEqual(result["status"], "error")
                self.assertIn("output exceeded", result["detail"])
                self.assertTrue(result["output_truncated"])
                self.assertLess(Path(result["log"]).stat().st_size,
                                batch.MAX_LOG_BYTES + 4096)

    @unittest.skipUnless(os.name == "posix", "process groups require POSIX")
    def test_timeout_kills_checker_and_child(self):
        started = time.monotonic()
        # Leave startup time for the fixture to create its child, while the
        # deadline remains below the child's one-second survival marker.
        result = self.case("timeout", "timeout", "--timeout", "0.8")
        self.assertEqual(result["status"], "timeout")
        self.assertLess(time.monotonic() - started, 3)
        pid = int((self.corpus / "timeout" / "broadcast.pid").read_text())
        self.assertGreater(pid, 0)
        # Works in sandboxes that disallow ps and on systems retaining zombies.
        # A surviving child writes this marker one second after starting.
        time.sleep(1.1)
        self.assertFalse((self.corpus / "timeout" / "broadcast.alive").exists(),
                         f"child {pid} still executing after timeout")

    def test_interruption_cancels_running_case(self):
        path = self.solution("interrupted", "timeout")
        stopped = threading.Event()
        stopped.set()
        result = batch.run_case(
            self.args(), path, "interrupted", "concurrent",
            self.output / "interrupted.log", stopped,
        )
        self.assertEqual(result["status"], "inconclusive")
        self.assertEqual(result["detail"], "batch interrupted")

    def test_complete_batch_reports_all_cases_sorted_and_keeps_errors(self):
        for name, mode in (("z", "missing"), ("a", "pass"), ("b", "fail"),
                           ("c", "inconclusive"), ("d", "unsupported")):
            self.solution(name, mode)
        with contextlib.redirect_stdout(io.StringIO()):
            code = batch.main([
                str(self.corpus.parent), "--binary", str(self.binary),
                "--output", str(self.output), "--jobs", "3", "--timeout", "3",
            ])
        self.assertEqual(code, 1)
        records = [json.loads(line) for line in (self.output / "results.jsonl").read_text().splitlines()]
        self.assertEqual(len(records), 25)
        summary = json.loads((self.output / "summary.json").read_text())
        self.assertEqual(summary["completed_cases"], 25)
        self.assertEqual(summary["expected_cases"], 25)
        self.assertEqual(summary["passed_submissions"], 1)
        self.assertEqual(list(summary["submissions"]), ["a", "b", "c", "d", "z"])
        self.assertEqual(summary["counts"], {
            "pass": 5, "fail": 5, "unsupported": 5, "inconclusive": 5, "error": 5,
            "send_budget": 0, "timeout": 0,
        })
        for submission in summary["submissions"].values():
            self.assertEqual([item["test"] for item in submission["results"]],
                             ["after_delivery", "concurrent", "reply", "reverse_reply", "sequential"])
            for item in submission["results"]:
                self.assertTrue(Path(item["log"]).is_file())

    def test_filters_and_all_pass_exit_status(self):
        self.solution("good")
        self.solution("bad", "fail")
        with contextlib.redirect_stdout(io.StringIO()):
            code = batch.main([
                str(self.corpus), "--binary", str(self.binary), "--output", str(self.output),
                "--submission", "good", "--test", "concurrent",
                "--test", "concurrent",
            ])
        self.assertEqual(code, 0)
        summary = json.loads((self.output / "summary.json").read_text())
        self.assertEqual(summary["expected_cases"], 1)
        self.assertEqual(summary["total_submissions"], 1)


if __name__ == "__main__":
    unittest.main()
