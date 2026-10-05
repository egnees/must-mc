//! One sender sends directly to every process, including itself. No faults yet.

use crate::proc::{Outputs, Process};

pub struct Direct {
    me: usize,
    nodes: usize,
}

impl Process for Direct {
    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
        outputs.send_local_message(message.to_string());
    }

    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs) {
        for to in 0..self.nodes {
            if to == self.me {
                outputs.send_local_message(message.to_string());
            } else {
                outputs.send_message(to, message.to_string());
            }
        }
    }
}

pub fn new(me: usize, nodes: usize) -> Box<dyn Process> {
    Box::new(Direct { me, nodes })
}
