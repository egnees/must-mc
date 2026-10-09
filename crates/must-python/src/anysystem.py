"""AnySystem callback API. Each replay gets a fresh copy of these classes."""
import json
import math
from typing import Any, Dict, List, Tuple, Union

JSON = Union[Dict[str, "JSON"], List["JSON"], str, int, float, bool, None]


class UnsupportedOperation(Exception):
    pass


class Message:
    _next_identity = 0

    def __init__(self, message_type, data):
        self._type = message_type
        self._data = data
        self._identity = Message._next_identity
        Message._next_identity += 1

    def __hash__(self):
        # Object identity equality, with an allocation-independent hash for sets.
        return self._identity

    @property
    def type(self):
        return self._type

    def get(self, key, default=None):
        return self._data.get(key, default)

    def remove(self, key):
        self._data.pop(key, None)

    def __contains__(self, key):
        return key in self._data

    def __getitem__(self, key):
        return self._data[key]

    def __setitem__(self, key, value):
        self._data[key] = value

    @staticmethod
    def from_json(message_type, json_str):
        return Message(message_type, json.loads(json_str))


class Context:
    def __init__(self, time, predicate=None):
        self._predicate = predicate
        self._time = time
        self._sent_messages = []
        self._sent_local_messages = []
        self._timer_actions = []
        self._bytes = 0
        self._count = 0
        self._unsupported_clock = False
        self._resource_limit = False

    def _record(self, group, action):
        self._count += 1
        self._bytes += len(json.dumps(action, ensure_ascii=True, allow_nan=False))
        if self._count > 10000 or self._bytes > 8 * 1024 * 1024:
            self._resource_limit = True
            raise MemoryError("callback action limit exceeded")
        group.append(action)

    def _message(self, msg):
        if not isinstance(msg.type, str):
            raise TypeError("message type has to be string")
        if len(msg.type) > 50:
            raise ValueError("message type length exceeds the limit of 50 characters")
        # Serialize immediately: mutation after send must not change the sent data.
        return {"kind": msg.type, "data": json.dumps(msg._data, ensure_ascii=True, allow_nan=False)}

    def set_predicate(self, predicate):
        """Set a pure Message -> bool receive filter; None accepts all.

        Rejected messages remain pending. The filter persists across callbacks
        until replaced and is evaluated against the current process state.
        """
        if predicate is not None and not callable(predicate):
            raise TypeError("receive predicate must be callable or None")
        self._predicate = predicate

    def send(self, msg, to):
        if not isinstance(to, str):
            raise TypeError("to argument has to be string")
        self._record(self._sent_messages, {"op": "send", "to": to, "message": self._message(msg)})

    def send_local(self, msg):
        self._record(self._sent_local_messages, {"op": "local", "message": self._message(msg)})

    def _timer(self, timer_name, delay, once):
        if not isinstance(timer_name, str):
            raise TypeError("timer_name argument has to be str")
        if len(timer_name) > 50:
            raise ValueError("timer_name length exceeds the limit of 50 characters")
        if not isinstance(delay, (int, float)) or not math.isfinite(delay) or delay < 0:
            raise ValueError("delay argument has to be finite and non-negative")
        self._record(self._timer_actions, {"op": "timer", "name": timer_name, "delay": delay, "once": once})

    def set_timer(self, timer_name, delay):
        self._timer(timer_name, delay, False)

    def set_timer_once(self, timer_name, delay):
        self._timer(timer_name, delay, True)

    def cancel_timer(self, timer_name):
        if not isinstance(timer_name, str):
            raise TypeError("timer_name argument has to be str")
        self._record(self._timer_actions, {"op": "cancel", "name": timer_name})

    def time(self):
        if self._time is None:
            self._unsupported_clock = True
            raise UnsupportedOperation("Context.time() requires a supplied model clock")
        return self._time

    def _actions(self):
        if self._resource_limit:
            raise MemoryError("callback action limit exceeded")
        if self._unsupported_clock:
            raise UnsupportedOperation("Context.time() requires a supplied model clock")
        # AnySystem drains these three groups in this order, not call order.
        return self._sent_messages + self._sent_local_messages + self._timer_actions


class Process:
    def on_start(self, ctx):
        pass

    def on_local_message(self, msg, ctx):
        raise NotImplementedError("on_local_message")

    def on_message(self, msg, sender, ctx):
        raise NotImplementedError("on_message")

    def on_timer(self, timer_name, ctx):
        raise NotImplementedError("on_timer")
