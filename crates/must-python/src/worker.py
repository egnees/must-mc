"""Persistent framed worker: states are histories, never pickles of Python objects."""
import importlib.util
import hashlib
import json
import os
import random
import struct
import sys
import traceback
import types
import typing
import uuid

MAX_FRAME = 8 * 1024 * 1024
path, class_name, seed, shim_source = sys.argv[1:]
seed = int(seed)
compiled = None
compiled_shim = compile(shim_source, "<must-python-anysystem>", "exec")
states = []
original_random = random.Random
protocol_input = os.fdopen(os.dup(0), "rb", buffering=0)
protocol_output = os.fdopen(os.dup(1), "wb", buffering=0)
# Includes direct os.write(1, ...) and third-party prints; protocol uses private fds.
with open(os.devnull, "r+b", buffering=0) as sink:
    os.dup2(sink.fileno(), 0)
    os.dup2(sink.fileno(), 1)
    os.dup2(sink.fileno(), 2)
sys.path.insert(0, os.path.dirname(path))
baseline_modules = set(sys.modules)


class DeterministicRandom(original_random):
    def seed(self, value=None, version=2):
        if value is None:
            value = random.getrandbits(256)
        return super().seed(value, version)


def reset(process_seed=seed):
    # Drop all modules imported by the previous local execution, including helper
    # files next to a submission. Standard modules used by the worker stay loaded.
    for name in tuple(sys.modules):
        if name not in baseline_modules:
            del sys.modules[name]
    random.Random = DeterministicRandom
    random.seed(process_seed)
    uuid.uuid4 = lambda: uuid.UUID(int=random.getrandbits(128), version=4)
    api = types.ModuleType("anysystem")
    sys.modules["anysystem"] = api
    exec(compiled_shim, api.__dict__)
    spec = importlib.util.spec_from_file_location("_must_solution", path)
    module = importlib.util.module_from_spec(spec)
    # Registration is required by dataclass and by normal Python imports.
    sys.modules[spec.name] = module
    exec(compiled, module.__dict__)
    return api, getattr(module, class_name)


def constructor_seed(encoded):
    args = json.loads(encoded)
    if not isinstance(args, list):
        raise TypeError("constructor arguments must be a JSON array")
    # Distinct process identities need distinct reproducible random streams:
    # giving every process the same seed would make their first UUIDs collide.
    normalized = json.dumps(args, ensure_ascii=True, separators=(",", ":"))
    return int.from_bytes(hashlib.sha256(
        str(seed).encode("ascii") + b"\0" + normalized.encode("ascii")
    ).digest(), "big")


def construct(encoded, process_seed):
    # Always parse fresh: constructors may mutate their argument objects.
    args = json.loads(encoded)
    api, cls = reset(process_seed)
    # PyO3 AnySystem passes the very same process-id strings from the process list.
    # Preserve that identity for constructors of the usual (id, process_ids) form.
    if len(args) == 2 and isinstance(args[0], str) and isinstance(args[1], list):
        for item in args[1]:
            if isinstance(item, str) and item == args[0]:
                args[0] = item
                break
    return api, cls(*args)


def callback(api, process, event):
    ctx = api.Context(event["time"])
    method = event["method"]
    if method == "on_start":
        fn = getattr(process, method, None)
        if fn is not None:
            fn(ctx)
    elif method == "on_timer":
        process.on_timer(event["name"], ctx)
    else:
        msg = api.Message.from_json(event["kind"], event["data"])
        if method == "on_message":
            process.on_message(msg, event["sender"], ctx)
        else:
            process.on_local_message(msg, ctx)
    return ctx._actions()


def request(req):
    global compiled
    op = req["op"]
    if op == "init":
        with open(path, "rb") as handle:
            compiled = compile(handle.read(), path, "exec")
        _, cls = reset()
        if not callable(cls):
            raise TypeError("requested process class is not callable")
        return {"ok": True}
    if op == "create":
        process_seed = constructor_seed(req["args"])
        construct(req["args"], process_seed)
        state = len(states)
        states.append((None, (req["args"], process_seed), None))
        return {"ok": True, "state": state, "actions": []}
    state = req["state"]
    history = []
    while states[state][0] is not None:
        parent, event, actions = states[state]
        history.append((event, actions))
        state = parent
    api, process = construct(*states[state][1])
    for event, expected in reversed(history):
        actual = callback(api, process, event)
        if actual != expected:
            raise RuntimeError("nondeterministic Python replay: callback outputs changed")
    event = req["event"]
    actions = callback(api, process, event)
    # Verify serializability/size before storing a node. The caller must never
    # observe a failed operation consuming a state id.
    response = {"ok": True, "state": len(states), "actions": actions}
    payload = encode(response)
    if len(payload) > MAX_FRAME:
        raise MemoryError("worker response exceeds frame limit")
    states.append((req["state"], event, actions))
    return payload


def encode(value):
    return json.dumps(value, ensure_ascii=True, allow_nan=False, separators=(",", ":")).encode("ascii")


def read_exact(size):
    parts = bytearray()
    while len(parts) < size:
        chunk = protocol_input.read(size - len(parts))
        if not chunk:
            raise EOFError()
        parts.extend(chunk)
    return bytes(parts)


while True:
    try:
        size = struct.unpack(">I", read_exact(4))[0]
        if size > MAX_FRAME:
            break
        req = json.loads(read_exact(size))
    except (EOFError, ValueError):
        break
    try:
        result = request(req)
    except BaseException as error:
        kind = "execution"
        if isinstance(error, MemoryError):
            kind = "resource"
        elif type(error).__name__ == "UnsupportedOperation" and type(error).__module__ == "anysystem":
            kind = "unsupported"
        detail = "".join(traceback.format_exception(
            type(error), error, error.__traceback__, limit=-12, chain=False
        ))
        result = {"ok": False, "kind": kind, "error": detail[-8192:]}
    try:
        payload = result if isinstance(result, bytes) else encode(result)
        if len(payload) > MAX_FRAME:
            payload = encode({"ok": False, "kind": "resource", "error": "worker response exceeds frame limit"})
        protocol_output.write(struct.pack(">I", len(payload)) + payload)
        protocol_output.flush()
    except (BrokenPipeError, OSError):
        break
