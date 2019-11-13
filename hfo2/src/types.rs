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

// TODO: Refactor type names and remove this.
#![allow(non_camel_case_types)]

use core::ffi;

use crate::page::*;

pub type c_void = ffi::c_void;
pub type c_int = i32;
pub type c_char = u8;
pub type size_t = usize;
pub type rsize_t = usize;
pub type uintptr_t = usize;

/// The ID of a VM. These are assigned sequentially.
pub type spci_vm_id_t = u16;
pub type spci_memory_handle_t = u32;

/// A count of VMs. This has the same range as the VM IDs but we give it a
/// different name to make the different semantics clear.
pub type spci_vm_count_t = spci_vm_id_t;

/// The index of a vCPU within a particular VM.
pub type spci_vcpu_index_t = u16;

/// A count of vCPUs. This has the same range as the vCPU indices but we give
/// it a different name to make the different semantics clear.
pub type spci_vcpu_count_t = spci_vcpu_index_t;

/// The ID of a interrupt. (TODO: Is it better to be `spci_intid_t`?)
pub type intid_t = u32;

pub const RSIZE_MAX: rsize_t = rsize_t::max_value() >> 1;

/// The number of virtual interrupt IDs which are supported.
pub const HF_NUM_INTIDS: intid_t = 64;

/// Interrupt ID returned when there is no interrupt pending.
pub const HF_INVALID_INTID: intid_t = 0xffff_ffff;

/// The virtual interrupt ID used for the virtual timer.
pub const HF_VIRTUAL_TIMER_INTID: intid_t = 3;

// TODO(HfO2): These constants are originally from build scripts. (See
// //project/reference/BUILD.gn.)
pub const HEAP_PAGES: usize = 60;

#[cfg(target_arch = "x86_64")]
pub const MAX_CPUS: usize = 4;

#[cfg(target_arch = "aarch64")]
pub const MAX_CPUS: usize = 8;

#[cfg(target_arch = "x86_64")]
pub const MAX_VMS: usize = 6;

#[cfg(target_arch = "aarch64")]
pub const MAX_VMS: usize = 16;

/// The ID of the primary VM which is responsible for scheduling.
pub const HF_PRIMARY_VM_ID: spci_vm_id_t = 0;

/// The amount of data that can be sent to a mailbox.
pub const HF_MAILBOX_SIZE: usize = PAGE_SIZE;

/// Sleep value for an indefinite period of time.
pub const HF_SLEEP_INDEFINITE: u64 = 0xff_ffff_ffff_ffff;
