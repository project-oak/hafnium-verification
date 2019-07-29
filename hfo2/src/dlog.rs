/*
 * Copyright 2019 Jeehoon Kang
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use core::fmt;

use crate::spinlock::*;
use crate::vm::*;

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

/// Send the contents of the given VM's log buffer to the log, preceded by the
/// VM ID and followed by a newline.
#[no_mangle]
pub unsafe extern "C" fn dlog_flush_vm_buffer(vm: VmLocked) {
    use core::fmt::Write;
    let mut writer = WRITER.lock();

    writer.write_str("VM ");
    writer.write_fmt(format_args!("{}", (*vm.vm).id));
    writer.write_str(": ");

    for i in 0..(*vm.vm).log_buffer_length {
        plat_console_putchar((*vm.vm).log_buffer[i]);
        (*vm.vm).log_buffer[i] = '\0' as u32 as u8;
    }

    (*vm.vm).log_buffer_length = 0;
    plat_console_putchar('\n' as u32 as u8);
}
