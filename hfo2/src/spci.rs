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

use core::marker::PhantomData;
use core::mem;

use crate::addr::*;
use crate::types::*;
use crate::vm::*;

pub const SPCI_VERSION_MAJOR: i32 = 0x0;
pub const SPCI_VERSION_MINOR: i32 = 0x9;
pub const SPCI_VERSION_MAJOR_OFFSET: usize = 16;

// SPCI return codes.
pub const SPCI_SUCCESS: i32 = 0;
pub const SPCI_NOT_SUPPORTED: i32 = -1;
pub const SPCI_INVALID_PARAMETERS: i32 = -2;
pub const SPCI_NO_MEMORY: i32 = -3;
pub const SPCI_BUSY: i32 = -4;
pub const SPCI_INTERRUPTED: i32 = -5;
pub const SPCI_DENIED: i32 = -6;
pub const SPCI_RETRY: i32 = -7;

/// Architected memory sharing message IDs.
#[repr(C)]
pub enum SpciMemoryShare {
    Donate = 0x2,
}

// SPCI function specific constants.
pub const SPCI_MSG_RECV_BLOCK_MASK: u32 = 0x1;
pub const SPCI_MSG_SEND_NOTIFY_MASK: u32 = 0x1;

pub const SPCI_MESSAGE_ARCHITECTED: usize = 0x0;
pub const SPCI_MESSAGE_IMPDEF: u16 = 0x1;
pub const SPCI_MESSAGE_IMPDEF_MASK: u16 = 0x1;

pub const SPCI_MSG_SEND_NOTIFY: u32 = 0x1;
pub const SPCI_MSG_RECV_BLOCK: u32 = 0x1;

/// The maximum length possible for a single message.
pub const SPCI_MSG_PAYLOAD_MAX: usize = HF_MAILBOX_SIZE - mem::size_of::<SpciMessage>();

// from inc/hf/spci_internal.h.
extern "C" {
    pub fn spci_msg_handle_architected_message(
        to_locked: VmLocked,
        from_locked: VmLocked,
        architected_message_replica: *const SpciArchitectedMessageHeader,
        from_message_replica: *mut SpciMessage,
        to_msg: *mut SpciMessage,
    ) -> spci_return_t;

    pub fn spci_msg_check_transition(
        to: *mut Vm,
        from: *mut Vm,
        share: SpciMemoryShare,
        orig_from_mode: *mut c_int,
        begin: ipaddr_t,
        end: ipaddr_t,
        memory_to_attributes: u32,
        from_mode: *mut c_int,
        to_mode: *mut c_int,
    ) -> bool;
}

/// SPCI common message header.
#[repr(C)]
pub struct SpciMessage {
    // TODO: version is part of SPCI alpha2 but will be
    // removed in the next spec revision hence we are not
    // including it in the header.
    /// flags[0]:
    ///     0: Architected message payload;
    ///     1: Implementation defined message payload.
    /// flags[15:1] reserved (MBZ).
    pub flags: u16,

    /// TODO: Padding is present to ensure controlled offset
    /// of the length field. SPCI spec must be updated
    /// to reflect this (TBD).
    reserved_1: u16,

    pub length: u32,
    pub target_vm_id: spci_vm_id_t,
    pub source_vm_id: spci_vm_id_t,

    /// TODO: Padding is present to ensure that the field
    /// payload alignment is 64B. SPCI spec must be updated
    /// to reflect this.
    reserved_2: u32,

    /// This field is originally a flexible array member in the C version code,
    /// but Rust has no corresponding representation of it. Declaring this as
    /// `payload: [u8]` makes any reference (even raw pointer) of SpciMessage
    /// being fat.
    /// Thus, don't make a variable with type `SpciMessage`. Usually that'll be
    /// not compatitable with `struct spci_message`.
    /// TODO: is here right place to use `Phantomdata`?
    pub payload: PhantomData<[u8]>,
}

#[repr(C)]
pub struct SpciArchitectedMessageHeader {
    r#type: u16,

    // TODO: Padding is present to ensure that the field payload is aligned on
    // a 64B boundary. SPCI spec must be updated to reflect this.
    reserved: [u16; 3],
    payload: PhantomData<[u8]>,
}

#[repr(C)]
pub struct SpciMemoryRegionConstituent {
    pub address: u64,
    pub page_count: u32,
    reserved: u32,
}

#[repr(C)]
pub struct SpciMemoryRegion {
    handle: spci_memory_handle_t,
    count: u32,
    pub constituents: PhantomData<[SpciMemoryRegionConstituent]>,
}

/// Obtain a pointer to the architected header in the spci_message.
///
/// Note: the argument "message" has const qualifier. This qualifier is meant
/// to forbid changes in information enclosed in the struct SpciMessage. The
/// SpciArchitectedMessageHeader, for which a pointer is returned in this
/// function, is not part of SpciMessage. Its information is meant to be
/// changed and hence the returned pointer does not have const type qualifier.
#[inline]
pub unsafe fn spci_get_architected_message_header(
    message: *const SpciMessage,
) -> *mut SpciArchitectedMessageHeader {
    &(*message).payload as *const _ as usize as *mut SpciArchitectedMessageHeader
}
