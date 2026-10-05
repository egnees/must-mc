//! Asynchronous transport with at most one permanent crash.
//!
//! In a faulty run, every normal terminal must contain that process's crash:
//! `recv` below never leaves it blocked forever. A separate run has no faulty node.
//!
//! Choose in advance which packets will still be in flight at the crash. Route
//! them to an inert sink, keeping each send in the 16-send budget. The Process
//! never sees these choices. Successful receives of the faulty node's packets
//! can all be ordered before its final crash; the remaining packets are lost
//! there. This preserves local histories for this asynchronous model with one
//! crash and no timers or failure notifications. It is not a general timed
//! network model. Loss follows the actual sending node, not the payload's author.

const LOST: usize = 3;

pub(super) fn add_sink(system: &mut must::System) {
    assert_eq!(system.add(|_| async {}), LOST);
}

pub(super) async fn send(ctx: &must::Ctx, to: usize, message: String, faulty: bool) {
    let destination = if faulty && ctx.nondet(["send", "lose-on-crash"]).await == "lose-on-crash" {
        ctx.insert_label(format!("lose-on-crash: {} -> {to}", ctx.tid()));
        LOST
    } else {
        to
    };
    ctx.send(destination, message, must::Model::Asyn);
}

pub(super) async fn recv(ctx: &must::Ctx, faulty: bool) -> Option<String> {
    if !faulty {
        return Some(ctx.recv_any().await);
    }

    // Abstract nonblocking receive: None chooses a crash, even if mail is
    // available. This is a fault choice in the test, not a protocol timeout.
    let message = ctx.recv_timeout_any().await;
    if message.is_none() {
        ctx.insert_label("crash");
    }
    message
}
