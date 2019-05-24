use core::fmt;

use crate::spinlock::*;

extern "C" {
    fn plat_console_putchar(c: u8);
}

struct Writer {}

impl Writer {
    const fn new() -> Self {
        Self {}
    }
}

impl fmt::Write for Writer {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for byte in s.bytes() {
            unsafe {
                plat_console_putchar(byte);
            }
        }
        Ok(())
    }
}

static WRITER: SpinLock<Writer> = SpinLock::new(Writer::new());

#[macro_export]
macro_rules! dlog {
    ($($arg:tt)*) => ($crate::dlog::_print(format_args!($($arg)*)));
}

#[doc(hidden)]
pub fn _print(args: fmt::Arguments) {
    use core::fmt::Write;
    WRITER.lock().write_fmt(args).unwrap();
}
