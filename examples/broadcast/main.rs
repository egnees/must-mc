mod cli;
mod proc;
mod python;
#[cfg(test)]
mod solutions;
mod tests;

#[cfg(not(feature = "system-allocator"))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> std::process::ExitCode {
    if cfg!(target_os = "linux") && !cfg!(feature = "system-allocator") {
        // SAFETY: set mimalloc's process-wide option before exploration starts.
        unsafe {
            libmimalloc_sys::mi_option_set_enabled(libmimalloc_sys::mi_option_large_os_pages, true);
        }
    }
    cli::run()
}
