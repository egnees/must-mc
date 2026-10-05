pub const THREADS: usize = 12;

pub async fn crash(ctx: &must::Ctx) -> bool {
    ctx.nondet(["continue", "crash"]).await == "crash"
}
