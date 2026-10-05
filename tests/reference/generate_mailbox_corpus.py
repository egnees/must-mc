#!/usr/bin/env python3
"""Reproduce production graph fixtures from the independent operational calendars.

Expected answers come from action-by-action operational enumeration, not the
production constraint compiler or its solver. Asyn includes full/blocked terminals;
the mixed Asyn/P2p corpus includes full terminals. Budgets fail generation.
"""
import importlib.util
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve()
STUDY = HERE.parents[3] / "independent-timing-study"
spec = importlib.util.spec_from_file_location("asyn_probe", STUDY / "asyn-timed-receives/probe.py")
asyn = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = asyn
spec.loader.exec_module(asyn)
base = asyn.base
send, recv = base.send, base.recv


def encode(p, rf, expected):
    lines = [f"{int(expected)} {len(p)}"]
    for thread in p:
        lines.append(str(len(thread)))
        for op in thread:
            if op.kind == "s":
                lines.append(f"s {op.lo} {op.hi} {op.wire} {op.dst} {op.val}")
            else:
                lines.append(f"{op.mode} {op.lo} {op.hi} {op.pred}")
    for r, source in sorted(rf.items()):
        lines.append("-1" if source is None else f"{source[0]} {source[1]}")
    return "\n".join(lines)


def main():
    corpus, accepted = [], 0
    programs = json.loads((STUDY / "asyn-timed-receives/corpus.json").read_text())
    for raw in programs:
        p = tuple(tuple(base.Op(**op) for op in th) for th in raw)
        expected, _ = asyn.calendar(p)
        for q, rf in asyn.terminal_candidates(p):
            answer = asyn.terminal_key(q, rf) in expected
            assert answer == asyn.scalar_solve(asyn.scalar_system(q, rf))
            corpus.append(encode(q, rf, answer))
            accepted += answer
    assert (len(corpus), accepted) == (1709, 1250)

    # Original P2p study seed and generator (203 programs, 669 candidate graphs).
    rng = random.Random(20260916)
    programs = []
    for mode in ("timeout", "poll"):
        for _ in range(100):
            threads = []
            for t in range(2):
                th = []
                for i in range(3):
                    lo = rng.randrange(3)
                    hi = lo + rng.randrange(2)
                    if rng.randrange(2):
                        th.append(send(rng.randrange(2), lo, hi, val=rng.choice(["x", "y"]), wire=rng.choice(["asyn", "p2p"])))
                    else:
                        th.append(recv(lo, hi, mode=mode, pred=rng.choice(["*", "x", "y"])))
                threads.append(tuple(th))
            programs.append(tuple(threads))
    programs += [
        ((send(1, 1, val="a", wire="p2p"), send(1, 2, val="b", wire="p2p")),
         (recv(mode="block", pred="b"), recv(mode="block", pred="a"))),
        ((recv(0), send(0, 0)),),
        ((send(1, 1, val="m", wire="p2p"), send(1, 1, val="n", wire="p2p")),
         (recv(mode="block", pred="n"), recv(0, pred="m"))),
    ]
    for p in programs:
        expected, _ = base.calendar(p)
        for rf in base.graph_choices(p):
            answer = base.key(rf) in expected
            assert answer == base.feasible(p, rf)
            corpus.append(encode(p, rf, answer))
            accepted += answer
    assert (len(corpus), accepted) == (2378, 1653)
    target = HERE.parents[1] / "fixtures/mailbox_oracle.txt"
    target.parent.mkdir(exist_ok=True)
    target.write_text(str(len(corpus)) + "\n" + "\n".join(corpus) + "\n")
    print(f"{len(corpus)} operational graph verdicts, {accepted} feasible; {target}")


if __name__ == "__main__":
    main()
