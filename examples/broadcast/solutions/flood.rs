//! Flood once to every peer before local delivery, with causal vector clocks.
//! Incorrect when in-flight messages can be lost after their sender crashes:
//! forwarding alone does not prove that any other process has received a copy.

use std::collections::BTreeMap;

use crate::proc::{Outputs, Process};

struct Message {
    clock: Vec<usize>,
    text: String,
}

struct Flood {
    me: usize,
    nodes: usize,
    sent: usize,
    delivered: Vec<usize>,
    pending: BTreeMap<(usize, usize), Message>,
}

impl Flood {
    fn receive(&mut self, sender: usize, clock: Vec<usize>, text: &str, outputs: &mut Outputs) {
        let id = (sender, clock[sender]);
        if id.1 <= self.delivered[sender] {
            return;
        }

        let first = !self.pending.contains_key(&id);
        let message = self.pending.entry(id).or_insert_with(|| Message {
            clock,
            text: text.to_owned(),
        });

        if first {
            let clock = message
                .clock
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(",");
            let wire = format!("{sender}|{clock}|{}", message.text);
            for to in 0..self.nodes {
                if to != self.me {
                    outputs.send_message(to, wire.clone());
                }
            }
        }
        self.deliver_ready(outputs);
    }

    fn deliver_ready(&mut self, outputs: &mut Outputs) {
        loop {
            let ready = self.pending.iter().find_map(|(&(sender, seq), message)| {
                let next = seq == self.delivered[sender] + 1;
                let dependencies = message
                    .clock
                    .iter()
                    .enumerate()
                    .all(|(node, &count)| node == sender || count <= self.delivered[node]);
                (next && dependencies).then_some((sender, seq))
            });
            let Some(id) = ready else { break };
            let message = self.pending.remove(&id).unwrap();
            self.delivered[id.0] = id.1;
            outputs.send_local_message(message.text);
        }
    }
}

impl Process for Flood {
    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs) {
        self.sent += 1;
        let mut clock = self.delivered.clone();
        clock[self.me] = self.sent;
        self.receive(self.me, clock, message, outputs);
    }

    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
        let mut fields = message.splitn(3, '|');
        let sender = fields.next().unwrap().parse().unwrap();
        let clock = fields
            .next()
            .unwrap()
            .split(',')
            .map(|value| value.parse().unwrap())
            .collect();
        let text = fields.next().unwrap();
        self.receive(sender, clock, text, outputs);
    }
}

pub fn new(me: usize, nodes: usize) -> Box<dyn Process> {
    assert!(me < nodes);
    Box::new(Flood {
        me,
        nodes,
        sent: 0,
        delivered: vec![0; nodes],
        pending: BTreeMap::new(),
    })
}
