//! Intentionally incorrect: reuse sequence numbers after clearing the outbox.
//! Otherwise the same majority ECHO and causal delivery as `causal`.

use std::collections::{BTreeMap, BTreeSet};

use crate::proc::{Outputs, Process};

struct Message {
    clock: Vec<usize>,
    text: String,
    echoes: BTreeSet<usize>,
}

struct Causal {
    me: usize,
    nodes: usize,
    delivered: Vec<usize>,
    pending: BTreeMap<(usize, usize), Message>, // (original sender, sequence number)
}

impl Causal {
    fn receive(
        &mut self,
        relay: usize,
        sender: usize,
        clock: Vec<usize>,
        text: &str,
        outputs: &mut Outputs,
    ) {
        let id = (sender, clock[sender]);
        if id.1 <= self.delivered[sender] {
            return;
        }

        let first = !self.pending.contains_key(&id);
        let message = self.pending.entry(id).or_insert_with(|| Message {
            clock,
            text: text.to_owned(),
            echoes: BTreeSet::from([self.me]), // Count our own copy, without sending to self.
        });
        message.echoes.insert(relay);

        if first {
            let clock = message
                .clock
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(",");
            let wire = format!("{}|{sender}|{clock}|{}", self.me, message.text);
            for to in 0..self.nodes {
                if to != self.me {
                    outputs.send_message(to, wire.clone());
                }
            }
        }
        // Forwarding must precede delivery, including if we crash halfway through the sends.
        self.deliver_ready(outputs);
    }

    fn deliver_ready(&mut self, outputs: &mut Outputs) {
        loop {
            let ready = self.pending.iter().find_map(|(&(sender, seq), message)| {
                let majority = message.echoes.len() > self.nodes / 2;
                let next = seq == self.delivered[sender] + 1;
                let dependencies = message
                    .clock
                    .iter()
                    .enumerate()
                    .all(|(node, &count)| node == sender || count <= self.delivered[node]);
                (majority && next && dependencies).then_some((sender, seq))
            });
            let Some(id) = ready else { break };
            let message = self.pending.remove(&id).unwrap();
            self.delivered[id.0] = id.1;
            outputs.send_local_message(message.text);
            // This delivery may unblock other pending messages.
        }
    }
}

impl Process for Causal {
    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs) {
        let mut clock = self.delivered.clone();
        // BUG: the pending outbox shrinks after delivery, so this reuses old IDs.
        clock[self.me] = self
            .pending
            .keys()
            .filter(|&&(sender, _)| sender == self.me)
            .count()
            + 1;
        self.receive(self.me, self.me, clock, message, outputs);
    }

    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
        // All peers use this format; splitn leaves arbitrary payload text intact.
        let mut fields = message.splitn(4, '|');
        let relay = fields.next().unwrap().parse().unwrap();
        let sender = fields.next().unwrap().parse().unwrap();
        let clock = fields
            .next()
            .unwrap()
            .split(',')
            .map(|value| value.parse().unwrap())
            .collect();
        let text = fields.next().unwrap();
        self.receive(relay, sender, clock, text, outputs);
    }
}

pub fn new(me: usize, nodes: usize) -> Box<dyn Process> {
    assert!(me < nodes);
    Box::new(Causal {
        me,
        nodes,
        delivered: vec![0; nodes],
        pending: BTreeMap::new(),
    })
}
