/// Causes execution to halt and prevent progress of the current and less privileged software
/// components. This should be triggered when a non-recoverable event is identified which leaves the
/// system in an inconsistent state.
///
/// TODO: Should this also reset the system?
#[cfg(not(feature = "test"))]
#[no_mangle]
pub unsafe extern "C" fn abort() -> ! {
    // TODO: Block all CPUs.
    loop {
        // Prevent loop being optimized away.
        asm!("nop");
    }
}
