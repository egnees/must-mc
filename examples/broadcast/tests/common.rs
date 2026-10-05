use std::sync::OnceLock;

static SETTINGS: OnceLock<(usize, usize)> = OnceLock::new();

pub fn configure(threads: usize, max_sends: usize) {
    SETTINGS
        .set((threads.max(1), max_sends))
        .expect("configure broadcast once");
}

pub fn threads() -> usize {
    SETTINGS.get().map_or(12, |settings| settings.0)
}

pub fn max_sends() -> usize {
    SETTINGS.get().map_or(16, |settings| settings.1)
}

pub async fn crash(ctx: &must::Ctx) -> bool {
    ctx.nondet(["continue", "crash"]).await == "crash"
}
