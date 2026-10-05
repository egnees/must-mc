//! Untimed safety checks: no duplication, no creation and causal delivery.
//! All three processes stay alive; messages may arrive in any order.

pub mod after_delivery;
mod common;
pub mod concurrent;
pub mod reply;
pub mod reverse_reply;
pub mod sequential;
