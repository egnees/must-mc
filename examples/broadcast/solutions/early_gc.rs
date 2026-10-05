//! Majority ECHO with premature garbage collection of causal dependencies.
//! Incorrectly treats ECHOs from every node as proof of local delivery everywhere.
//! A late ECHO can therefore erase a dependency before the next broadcast.

use std::collections::{BTreeMap, BTreeSet};

use crate::proc::{Outputs, Process};

struct Message {
    clock: Vec<usize>,
    text: String,
    echoes: BTreeSet<usize>,
}

struct EarlyGc {
    me: usize,
    nodes: usize,
    sent: usize,
    delivered: Vec<usize>,
    seen_by_all: Vec<usize>,
    delivered_echoes: BTreeMap<(usize, usize), BTreeSet<usize>>,
    pending: BTreeMap<(usize, usize), Message>,
}

impl EarlyGc {
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
            if let Some(echoes) = self.delivered_echoes.get_mut(&id) {
                echoes.insert(relay);
                if echoes.len() == self.nodes {
                    self.seen_by_all[sender] = self.seen_by_all[sender].max(id.1);
                    self.delivered_echoes.remove(&id);
                }
            }
            return;
        }

        let first = !self.pending.contains_key(&id);
        let message = self.pending.entry(id).or_insert_with(|| Message {
            clock,
            text: text.to_owned(),
            echoes: BTreeSet::from([self.me]),
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
            if message.echoes.len() == self.nodes {
                self.seen_by_all[id.0] = self.seen_by_all[id.0].max(id.1);
            } else {
                self.delivered_echoes.insert(id, message.echoes);
            }
            outputs.send_local_message(message.text);
        }
    }
}

impl Process for EarlyGc {
    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs) {
        self.sent += 1;
        let mut clock = self.delivered.clone();
        // BUG: every node has seen these messages, but may not have delivered them.
        for (node, count) in clock.iter_mut().enumerate() {
            if *count <= self.seen_by_all[node] {
                *count = 0;
            }
        }
        clock[self.me] = self.sent;
        self.receive(self.me, self.me, clock, message, outputs);
    }

    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
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
    Box::new(EarlyGc {
        me,
        nodes,
        sent: 0,
        delivered: vec![0; nodes],
        seen_by_all: vec![0; nodes],
        delivered_echoes: BTreeMap::new(),
        pending: BTreeMap::new(),
    })
}
