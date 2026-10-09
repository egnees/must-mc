from causal import BroadcastProcess as CausalBroadcast


class BroadcastProcess(CausalBroadcast):
    def accepts(self, message):
        author = message["author"]
        return message["clock"][author] > self.delivered[author]

    def on_start(self, ctx):
        ctx.set_predicate(self.accepts)

    def on_local_message(self, message, ctx):
        super().on_local_message(message, ctx)
        ctx.set_predicate(self.accepts)

    def on_message(self, message, sender, ctx):
        super().on_message(message, sender, ctx)
        ctx.set_predicate(self.accepts)
