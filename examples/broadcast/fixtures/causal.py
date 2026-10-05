from anysystem import Message, Process


class BroadcastProcess(Process):
    def __init__(self, process_id, processes):
        self.me = int(process_id)
        self.nodes = len(processes)
        self.sent = 0
        self.delivered = [0] * self.nodes
        self.pending = {}

    def on_start(self, ctx):
        pass

    def on_timer(self, name, ctx):
        pass

    def on_local_message(self, message, ctx):
        self.sent += 1
        clock = list(self.delivered)
        clock[self.me] = self.sent
        self.receive(self.me, self.me, clock, message["text"], ctx)

    def on_message(self, message, sender, ctx):
        self.receive(int(sender), message["author"], message["clock"], message["text"], ctx)

    def receive(self, relay, author, clock, text, ctx):
        key = (author, clock[author])
        if key[1] <= self.delivered[author]:
            return
        first = key not in self.pending
        if first:
            self.pending[key] = (clock, text, {self.me})
        self.pending[key][2].add(relay)
        if first:
            message = Message("ECHO", {"author": author, "clock": clock, "text": text})
            for node in range(self.nodes):
                if node != self.me:
                    ctx.send(message, str(node))
        while True:
            ready = None
            for key in sorted(self.pending):
                clock, text, echoes = self.pending[key]
                author, seq = key
                if (len(echoes) > self.nodes / 2
                        and seq == self.delivered[author] + 1
                        and all(node == author or count <= self.delivered[node]
                                for node, count in enumerate(clock))):
                    ready = key
                    break
            if ready is None:
                return
            clock, text, echoes = self.pending.pop(ready)
            self.delivered[ready[0]] = ready[1]
            ctx.send_local(Message("DELIVER", {"text": text}))
