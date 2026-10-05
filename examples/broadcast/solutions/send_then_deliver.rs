//! Send to every peer before delivering locally. No forwarding after sender failure.

use crate::proc::{Outputs, Process};

pub struct SendThenDeliver {
    me: usize,
    nodes: usize,
}

impl Process for SendThenDeliver {
    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs) {
        for to in 0..self.nodes {
            if to != self.me {
                outputs.send_message(to, message.to_string());
            }
        }
        outputs.send_local_message(message.to_string());
    }

    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
        outputs.send_local_message(message.to_string());
    }
}

pub fn new(me: usize, nodes: usize) -> Box<dyn Process> {
    Box::new(SendThenDeliver { me, nodes })
}
