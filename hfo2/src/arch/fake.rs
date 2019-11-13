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

// TODO: Refactor type names and remove this.
#![allow(non_camel_case_types)]

use crate::types::*;

/// The integer type corresponding to the native register size.
pub type uintreg_t = u64;

/// The ID of a physical or virtual CPU.
pub type cpu_id_t = u32;

/// Integer type large enough to hold a physical address.
pub type uintpaddr_t = uintptr_t;

/// Integer type large enough to hold a virtual address.
pub type uintvaddr_t = uintptr_t;

/// The type of a page table entry (PTE).
pub type pte_t = u64;

/// Arch-specific information about a VM.
#[repr(C)]
pub struct ArchVm {
    dummy: *mut c_void,
}

/// Types to represent the register state of a VM.
#[repr(C)]
#[derive(Default)]
pub struct ArchRegs {
    r: [uintreg_t; 5],
    vcpu_id: cpu_id_t,
    virtual_interrupt: bool,
}

pub fn arch_cpu_module_init() {
    // Do nothing.
}

// TODO(HfO2): Following functions are empty, since linker complains if the
// implementations of functions are missing even they're never called in the
// unit tests. Make a custom target and remove those (#46.)
#[no_mangle]
pub extern "C" fn arch_one_time_init() {
    unreachable!();
}
