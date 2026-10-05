"""Independent bounded operational interpreter for timed Mbox/P2p/Asyn.

Global physical send order is recorded by execution, not guessed by constraints.
FIFO deliveries use the order of already executed Mbox sends to one destination.
No production code, ranks, difference constraints or pruning certificates are used.
"""


def calendar(base, p, cap=300_000):
    a = base.ops(p)
    # time, program counters, pending receives, deliveries, delivered set, RF, send log
    todo = [(0, (0,) * len(p), (None,) * len(p), (), (), (), ())]
    seen, terminals = set(), set()
    while todo:
        state = todo.pop()
        if state in seen:
            continue
        seen.add(state)
        assert len(seen) <= cap, "Mbox calendar budget exceeded"
        now, pcs, waiting, arrival_items, delivered_items, rf_items, sent = state
        arrivals, delivered, rf = dict(arrival_items), set(delivered_items), dict(rf_items)

        def emit(pc=pcs, wait=waiting, ar=arrivals, dl=delivered, rr=rf, sends=sent, time=now):
            todo.append((time, tuple(pc), tuple(wait), tuple(sorted(ar.items())),
                         tuple(sorted(dl)), base.key(rr), tuple(sends)))

        def fifo_before(m, s):
            if a[m].wire != a[s].wire or a[m].dst != a[s].dst:
                return False
            if a[s].wire == "mbox":
                return sent.index(m) < sent.index(s)
            return a[s].wire == "p2p" and m[0] == s[0] and m[1] < s[1]

        def eligible(r, dl=delivered):
            candidates = [s for s in dl if s not in rf.values() and base.matches(a, s, r)]
            return [s for s in candidates if not any(fifo_before(m, s) for m in candidates)]

        def finish(t, source, dl=delivered):
            pc, wait, rr = list(pcs), list(waiting), dict(rf)
            rr[t, pc[t]] = source
            pc[t] += 1
            wait[t] = None
            emit(pc=pc, wait=wait, dl=dl, rr=rr)

        had_action = False
        for t, th in enumerate(p):
            if pcs[t] == len(th) or waiting[t] is not None:
                continue
            had_action = True
            e, op = (t, pcs[t]), th[pcs[t]]
            if op.kind == "s":
                for delay in range(op.lo, op.hi + 1):
                    at = now + delay
                    # e is being appended to the actual global sending sequence now.
                    if any(a[m].wire == op.wire and a[m].dst == op.dst and previous > at
                           and (op.wire == "mbox" or (op.wire == "p2p" and m[0] == t))
                           for m, previous in arrivals.items()):
                        continue
                    pc, ar = list(pcs), dict(arrivals)
                    pc[t] += 1
                    ar[e] = at
                    emit(pc=pc, ar=ar, sends=sent + (e,))
            elif op.mode != "poll" and eligible(e):
                for s in eligible(e):
                    finish(t, s)
            elif op.mode == "block":
                wait = list(waiting)
                wait[t] = ("block", None)
                emit(wait=wait)
            else:
                for delay in range(op.lo, op.hi + 1):
                    wait = list(waiting)
                    wait[t] = (op.mode, now + delay)
                    emit(wait=wait)
        for s, at in arrivals.items():
            if at != now or s in delivered:
                continue
            if any(fifo_before(m, s) and m not in delivered for m in sent):
                continue
            had_action = True
            dl, t = delivered | {s}, a[s].dst
            if waiting[t] is not None and waiting[t][0] != "poll" and base.matches(a, s, (t, pcs[t])):
                for m in eligible((t, pcs[t]), dl):
                    finish(t, m, dl)
            else:
                emit(dl=dl)
        for t, w in enumerate(waiting):
            if w is None or w[1] != now:
                continue
            had_action = True
            candidates = eligible((t, pcs[t]))
            if w[0] == "timeout":
                assert not candidates
                finish(t, None)
            else:
                for s in candidates or [None]:
                    finish(t, s)
        if not had_action:
            future = [at for s, at in arrivals.items() if s not in delivered and at > now]
            future += [w[1] for w in waiting if w is not None and w[1] is not None and w[1] > now]
            if future:
                emit(time=min(future))
            elif len(delivered) == len(arrivals) and all(pc == len(th) for pc, th in zip(pcs, p)):
                terminals.add(base.key(rf))
    return terminals, len(seen)
