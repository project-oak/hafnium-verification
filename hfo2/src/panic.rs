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
