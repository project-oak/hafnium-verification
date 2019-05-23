use core::panic::PanicInfo;

use crate::utils::*;

#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    spin_loop()
}
