"""Persistent history worker with opt-in audited value-state interning."""
import importlib.util
import collections
import hashlib
import json
import marshal
import os
import random
import struct
import sys
import traceback
import types
import typing
import uuid

MAX_FRAME = 8 * 1024 * 1024
path, class_name, seed, shim_source, semantic_enabled = sys.argv[1:]
semantic_enabled = semantic_enabled == "true"
semantic_contract = False
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


def callback(api, process, event, predicate):
    ctx = api.Context(event["time"], predicate)
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
    return ctx._actions(), ctx._predicate


def semantic_key(api, process, predicate, root):
    """Exact, collision-free value graph under the explicit pure-value-v1 contract.

    This is NOT a serializer for arbitrary Python. The opt-in promises callbacks
    depend only on process fields and input, no global/class writes, randomness,
    object identity/hash, interpreter inspection, or observable set iteration.
    Sets may be used for membership/len only (or sorted before traversal).
    Dict/list order and mutable alias topology remain observable and are encoded.
    Unknown objects/closures conservatively keep the ordinary history cursor.
    No execution graph or callback/action is removed by this cache.
    """
    if not semantic_enabled or not semantic_contract:
        return None
    def plain_record_class(typ):
        for base in typ.__mro__:
            if base is object:
                continue
            attrs = base.__dict__
            slots = attrs.get("__slots__", ())
            slots = (slots,) if isinstance(slots, str) else slots
            if any(slot not in ("__dict__", "__weakref__") for slot in slots):
                return False
            if "__getattribute__" in attrs or "__getattr__" in attrs:
                return False
            if any(hasattr(attr, "__get__")
                   and not isinstance(attr, (types.FunctionType, staticmethod, classmethod))
                   for name, attr in attrs.items()
                   if name not in ("__dict__", "__weakref__")):
                return False
        return True

    # Process inherits an instance dict from the API even if the submission adds
    # slots. Those slots are hidden from __dict__, so never intern such a process.
    if not plain_record_class(type(process)) or not hasattr(process, "__dict__"):
        return None
    seen = {}

    def fixed_record_class(typ):
        # A local factory can create distinct classes with the same qualname
        # but different method closures. Only immutable module-bound classes
        # have behavior fixed by the audited source across every history.
        resolved = sys.modules.get("_must_solution")
        for name in typ.__qualname__.split("."):
            if name == "<locals>" or resolved is None:
                return False
            resolved = getattr(resolved, name, None)
        return resolved is typ

    if (type(process) is not getattr(sys.modules["_must_solution"], class_name)
            or not fixed_record_class(type(process))):
        return None

    def value(obj):
        typ = type(obj)
        if obj is None or typ in (bool, int, str):
            return [typ.__name__, obj]
        if typ is float:
            # hex() collapses NaN signs/payloads, observable by pure arithmetic.
            # Container equality observes NaN aliases even without explicit
            # identity use. Conservatively retain history caching for all NaNs.
            if obj != obj:
                raise TypeError("NaN state value")
            return ["float", struct.pack("!d", obj).hex()]
        # Immutable, source-audited helper record classes (e.g. MessageState).
        # Descriptors, slots and custom attribute access are deliberately excluded.
        record = (typ.__module__ == "_must_solution" and fixed_record_class(typ) and obj is not process
                  and plain_record_class(typ) and hasattr(obj, "__dict__"))
        if typ in (list, dict, set, tuple, frozenset, collections.defaultdict) or obj is process or typ is api.Message or record:
            identity = id(obj)
            if identity in seen:
                return ["ref", seen[identity]]
            index = len(seen)
            seen[identity] = index
            if obj is process:
                return ["process", index, value(obj.__dict__)]
            if record:
                return ["record", index, typ.__qualname__, value(obj.__dict__)]
            if typ is api.Message:
                # Allocation identity is unobservable by the audited contract.
                return ["message", index, [[value(k), value(v)] for k, v in obj.__dict__.items()
                                           if k != "_identity"]]
            if typ in (dict, collections.defaultdict):
                return [typ.__name__, index,
                        value(obj.default_factory) if typ is collections.defaultdict else None,
                        [[value(k), value(v)] for k, v in obj.items()]]
            if typ in (set, frozenset):
                # Restrict set contents to immutable scalar/tuple values. Sorting
                # never invokes submission code or discards mutable aliasing.
                def member(item):
                    if type(item) is tuple:
                        return ["tuple", [member(x) for x in item]]
                    if item is None or type(item) in (bool, int, str, float):
                        return value(item)
                    raise TypeError("unsupported set member")
                members = [member(item) for item in obj]
                members.sort(key=lambda item: json.dumps(item, ensure_ascii=True))
                return [typ.__name__, index, members]
            return [typ.__name__, index, [value(item) for item in obj]]
        if typ is type and obj in (list, dict, set, tuple, frozenset, int, float, str):
            return ["builtin-factory", obj.__name__]
        if typ is types.MethodType:
            return ["method", value(obj.__func__), value(obj.__self__)]
        if typ is types.CodeType:
            # Includes exception tables and source locations, not only bytecode.
            # All workers run the same interpreter/source; this is never loaded.
            return ["code", marshal.dumps(obj).hex()]
        if typ is types.CellType:
            identity = id(obj)
            if identity in seen:
                return ["ref", seen[identity]]
            index = len(seen)
            seen[identity] = index
            return ["cell", index, value(obj.cell_contents)]
        if typ is types.FunctionType and obj.__module__ == "_must_solution":
            # A function may spoof __module__ while carrying a private globals
            # dict. Its code/defaults/closure do not describe those dependencies;
            # only the audited solution's fixed module namespace is supported.
            if obj.__globals__ is not sys.modules["_must_solution"].__dict__:
                raise TypeError("private function globals")
            identity = id(obj)
            if identity in seen:
                return ["ref", seen[identity]]
            index = len(seen)
            seen[identity] = index
            if obj.__dict__:
                raise TypeError("function attributes")
            # The module/code is fixed. Include exact code, defaults and
            # closure cells; a closure referring to self uses the same alias map.
            return ["function", index, value(obj.__code__),
                    value(obj.__defaults__), value(obj.__kwdefaults__),
                    [value(cell) for cell in (obj.__closure__ or ())]]
        if typ is getattr(api, "SenderPredicate", None):
            return ["sender-predicate", value(obj.predicate)]
        raise TypeError("unsupported state object")

    try:
        payload = json.dumps([states[root][1], value(process), value(predicate)],
                             ensure_ascii=True, allow_nan=False, separators=(",", ":"))
        # Large states retain history caching rather than exceed framing limits.
        return payload if len(payload) <= MAX_FRAME // 2 else None
    except (TypeError, ValueError, RecursionError):
        return None


def request(req):
    global compiled, semantic_contract
    op = req["op"]
    if op == "init":
        with open(path, "rb") as handle:
            compiled = compile(handle.read(), path, "exec")
        _, cls = reset()
        semantic_contract = getattr(sys.modules["_must_solution"], "__must_state_cache__", None) == "pure-value-v1"
        if not callable(cls):
            raise TypeError("requested process class is not callable")
        return {"ok": True}
    if op == "create":
        process_seed = constructor_seed(req["args"])
        api, process = construct(req["args"], process_seed)
        state = len(states)
        states.append((None, (req["args"], process_seed), None))
        return {"ok": True, "state": state, "actions": [], "semantic_key": semantic_key(api, process, None, state)}
    predicate = None
    state = req["state"]
    imported = []
    nodes = req.get("import", [])
    if state is None:
        args = nodes[0]["args"]
        process_seed = constructor_seed(args)
        api, process = construct(args, process_seed)
        state = len(states)
        states.append((None, (args, process_seed), None))
        imported.append(state)
        root = state
        nodes = nodes[1:]
    else:
        history = []
        root = state
        while states[root][0] is not None:
            parent, event, actions = states[root]
            history.append((event, actions))
            root = parent
        api, process = construct(*states[root][1])
        for event, expected in reversed(history):
            actual, predicate = callback(api, process, event, predicate)
            if [actual, predicate is not None] != expected:
                raise RuntimeError("nondeterministic Python replay: callback outputs changed")
    for node in nodes:
        actions, predicate = callback(api, process, node["event"], predicate)
        expected = [actions, predicate is not None]
        if expected != node["expected"]:
            raise RuntimeError("nondeterministic Python replay: imported callback outputs changed")
        next_state = len(states)
        states.append((state, node["event"], expected))
        state = next_state
        imported.append(state)
    if op == "predicate":
        msg = api.Message.from_json(req["kind"], req["data"])
        accepted = api._matches_predicate(predicate, msg, req.get("sender"))
        if not isinstance(accepted, bool):
            raise TypeError("receive predicate must return bool")
        return {"ok": True, "accepted": accepted, "imported": imported}
    event = req["event"]
    actions, predicate = callback(api, process, event, predicate)
    # Publish the new callback only after validating its response.
    response = {"ok": True, "state": len(states), "actions": actions, "has_predicate": predicate is not None, "imported": imported, "semantic_key": semantic_key(api, process, predicate, root)}
    payload = encode(response)
    if len(payload) > MAX_FRAME:
        raise MemoryError("worker response exceeds frame limit")
    states.append((state, event, [actions, predicate is not None]))
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
