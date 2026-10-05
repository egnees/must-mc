#!/usr/bin/env python3
"""Generate Mbox/mixed graph verdicts from the independent operational calendar."""
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True

from generate_mailbox_corpus import base, encode, send, recv
from mbox_calendar import calendar


def main():
    rng = random.Random(2026091617)
    programs = []
    for mode in ("timeout", "poll"):
        for _ in range(100):
            ths = []
            for t in range(2):
                th = []
                for _ in range(3):
                    lo = rng.randrange(3)
                    hi = lo + rng.randrange(2)
                    if rng.randrange(2):
                        th.append(send(rng.randrange(2),lo,hi,val=rng.choice(["x","y"]),wire=rng.choice(["asyn","p2p","mbox"])))
                    else:
                        th.append(recv(lo,hi,mode=mode,pred=rng.choice(["*","x","y"])))
                ths.append(tuple(th))
            programs.append(tuple(ths))
    programs += [
        ((send(2,10,wire="mbox"),),(recv(2,mode="poll",pred="absent"),send(2,1,wire="mbox")),()),
        ((send(2,10,wire="mbox"),),(send(2,1,wire="mbox"),),(recv(mode="block"),)),
        ((send(1,1,val="m",wire="mbox"),send(1,1,val="n",wire="mbox")),(recv(mode="block",pred="n"),recv(0,pred="m"))),
        ((send(1,10,wire="mbox"),send(2,1,wire="mbox")),(),()),
    ]
    corpus, accepted, states = [], 0, 0
    for p in programs:
        expected, visited = calendar(base,p)
        states += visited
        # base.graph_choices uses Asyn for unknown models: includes every well-formed
        # Mbox candidate. Invalid untimed Mbox choices have expected=False, by execution.
        candidates = set()
        for rf in base.graph_choices(p):
            candidates.add(base.key(rf))
            answer = base.key(rf) in expected
            corpus.append(encode(p,rf,answer))
            accepted += answer
        assert expected <= candidates, "oracle execution missing from candidate set"
    target = Path(__file__).resolve().parents[1] / "fixtures/mbox_oracle.txt"
    target.write_text(str(len(corpus))+"\n"+"\n".join(corpus)+"\n")
    print(f"{len(programs)} programs, {len(corpus)} candidates, {accepted} feasible, {states} operational states")


if __name__ == "__main__":
    main()
