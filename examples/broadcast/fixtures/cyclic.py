"""A repeated value state must keep emitting messages until the send budget."""
from anysystem import Message, Process

__must_state_cache__ = "pure-value-v1"


class BroadcastProcess(Process):
    def __init__(self, proc_id, processes):
        self.proc_id = proc_id

    def on_local_message(self, msg, ctx):
        ctx.send(Message("BCAST", {"text": msg["text"]}), self.proc_id)

    def on_message(self, msg, sender, ctx):
        ctx.send(msg, self.proc_id)

    def on_timer(self, name, ctx):
        pass
