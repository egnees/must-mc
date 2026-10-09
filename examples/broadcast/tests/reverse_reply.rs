use super::common;
use crate::proc::Factory;

pub fn run(factory: Factory) -> Result<usize, String> {
    common::run(|| common::reply_system(factory.clone(), 1, 0))
        .map_err(|error| format!("reverse_reply: {error}"))
}
