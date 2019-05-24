#[allow(unused)]
fn abort_impl() -> ! {
    // TODO: Block all CPUs.
    crate::utils::spin_loop()
}

/// Causes execution to halt and prevent progress of the current and less privileged software
/// components. This should be triggered when a non-recoverable event is identified which leaves the
/// system in an inconsistent state.
///
/// TODO: Should this also reset the system?
#[cfg(not(feature = "test"))]
#[no_mangle]
pub extern "C" fn abort() -> ! {
    abort_impl()
}

#[cfg(not(test))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    dlog!("Panic: {:?}\n", info);
    abort_impl()
}
