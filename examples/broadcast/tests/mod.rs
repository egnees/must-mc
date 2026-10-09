//! Safety and liveness in five asynchronous broadcast scenarios.
//! Crash cuts cover at most one failed process without enumerating faults.

pub mod after_delivery;
pub mod common;
pub mod concurrent;
mod cuts;
pub mod reply;
pub mod reverse_reply;
pub mod sequential;

pub type Scenario = fn(crate::proc::Factory) -> Result<usize, String>;

pub const SCENARIOS: [(&str, Scenario); 5] = [
    ("concurrent", concurrent::run),
    ("reply", reply::run),
    ("reverse_reply", reverse_reply::run),
    ("sequential", sequential::run),
    ("after_delivery", after_delivery::run),
];

#[cfg(test)]
mod solutions;
