from anysystem import Message, Process


class BroadcastProcess(Process):
    def __init__(self, process_id, processes):
        self.processes = processes

    def on_start(self, ctx):
        ctx.set_predicate(self.accepts)

    def accepts(self, message):
        raise ValueError("broken receive predicate")

    def on_local_message(self, message, ctx):
        for process in self.processes:
            ctx.send(Message("BCAST", {}), process)

    def on_message(self, message, sender, ctx):
        pass
