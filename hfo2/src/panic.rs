use core::panic::PanicInfo;

use crate::utils::*;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    spin_loop()
}
