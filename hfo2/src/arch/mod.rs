/*
 * Copyright 2019 Sanguk Park.
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

#[cfg(target_arch = "aarch64")]
mod aarch64;

#[cfg(target_arch = "x86_64")]
mod fake;

#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

#[cfg(target_arch = "x86_64")]
pub use fake::*;

// from inc/hf/arch/timer.h
extern "C" {

    pub fn arch_timer_mask(regs: *mut ArchRegs);
    /// Checks whether the virtual timer is enabled and its interrupt not
    /// masked.
    pub fn arch_timer_enabled(regs: *const ArchRegs) -> bool;

    /// Returns the number of nanoseconds remaining on the virtual timer as
    /// stored in the given `ArchRegs`, or 0 if it has already expired. This is
    /// undefined if the timer is not enabled.
    pub fn arch_timer_remaining_ns(regs: *const ArchRegs) -> u64;

    /// Returns whether the timer is ready to fire: i.e. it is enabled, not
    /// masked, and the condition is met.
    pub fn arch_timer_pending(regs: *const ArchRegs) -> bool;

    /// Checks whether the virtual timer is enabled and its interrupt not
    /// maksed, for the currently active vCPU.
    pub fn arch_timer_enabled_current() -> bool;

    /// Disable the virtual timer for the currently active vCPU.
    pub fn arch_timer_disable_current();

    pub fn arch_timer_remaining_ticks_current() -> u64;

    /// Returns the number of nanoseconds remaining on the virtual timer of the
    /// currently active vCPU, or 0 if it has already expired. This is undefined
    /// if the timer is not enabled.
    pub fn arch_timer_remaining_ns_current() -> u64;
}
