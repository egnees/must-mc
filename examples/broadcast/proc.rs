use std::sync::Arc;

pub type Factory = Arc<dyn Fn(usize, usize) -> Box<dyn Process> + Send + Sync>;
pub type ReceivePredicate = Arc<dyn Fn(&str) -> bool + Send + Sync>;

#[derive(Default)]
pub struct Outputs {
    actions: Vec<Output>,
}

pub(crate) enum Output {
    Message { to: usize, message: String },
    LocalMessage(String),
    Error(String),
}

impl Outputs {
    pub(crate) fn take(&mut self) -> Vec<Output> {
        std::mem::take(&mut self.actions)
    }

    pub fn error(&mut self, message: String) {
        self.actions.push(Output::Error(message));
    }

    pub fn send_message(&mut self, to: usize, message: String) {
        self.actions.push(Output::Message { to, message });
    }

    pub fn send_local_message(&mut self, message: String) {
        self.actions.push(Output::LocalMessage(message));
    }
}

pub trait Process {
    fn receive_predicate(&self) -> Option<ReceivePredicate> {
        None
    }

    fn on_message(&mut self, message: &str, outputs: &mut Outputs);

    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs);
}
