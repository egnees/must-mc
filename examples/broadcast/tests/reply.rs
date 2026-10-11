use super::common;
use crate::proc::Factory;

pub fn run(factory: Factory) -> Result<(), String> {
    common::run(|| common::reply_system(factory.clone(), 0, 1))
        .map_err(|error| format!("reply: {error}"))
}
