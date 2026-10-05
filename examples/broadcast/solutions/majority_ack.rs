//! One broadcast: followers deliver DATA immediately; the sender waits for a majority
//! of distinct acknowledgements, counting itself. ACKs are protocol messages only.
//! This deliberately has no forwarding to recover a partially completed broadcast.

use crate::proc::{Outputs, Process};

pub struct MajorityAck {
    me: usize,
    nodes: usize,
    outstanding: Option<String>,
    votes: Vec<bool>,
    delivered: bool,
}

impl MajorityAck {
    fn deliver_if_majority(&mut self, outputs: &mut Outputs) {
        if !self.delivered && self.votes.iter().filter(|&&vote| vote).count() > self.nodes / 2 {
            if let Some(message) = &self.outstanding {
                outputs.send_local_message(message.clone());
                self.delivered = true;
            }
        }
    }
}

impl Process for MajorityAck {
    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs) {
        // The example supports one input broadcast, not concurrent broadcast instances.
        if self.outstanding.is_some() || self.delivered {
            return;
        }
        self.outstanding = Some(message.to_string());
        self.votes[self.me] = true;
        for to in 0..self.nodes {
            if to != self.me {
                outputs.send_message(to, format!("DATA:{}:{message}", self.me));
            }
        }
        self.deliver_if_majority(outputs);
    }

    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
        // splitn preserves payloads containing colons, including an empty payload.
        let mut fields = message.splitn(3, ':');
        let Some(kind) = fields.next() else { return };
        let Some(peer) = fields.next().and_then(|value| value.parse::<usize>().ok()) else {
            return;
        };
        let Some(payload) = fields.next() else { return };
        if peer >= self.nodes || peer == self.me {
            return;
        }
        match kind {
            "DATA" if self.outstanding.is_none() && !self.delivered => {
                outputs.send_local_message(payload.to_string());
                self.delivered = true;
                outputs.send_message(peer, format!("ACK:{}:{payload}", self.me));
            }
            "ACK" if self.outstanding.as_deref() == Some(payload) => {
                self.votes[peer] = true;
                self.deliver_if_majority(outputs);
            }
            _ => {}
        }
    }
}

pub fn new(me: usize, nodes: usize) -> Box<dyn Process> {
    assert!(me < nodes, "process id must belong to the broadcast group");
    Box::new(MajorityAck {
        me,
        nodes,
        outstanding: None,
        votes: vec![false; nodes],
        delivered: false,
    })
}
