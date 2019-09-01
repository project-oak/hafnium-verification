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

use core::convert::TryFrom;
use core::mem;

use crate::mm::*;
use crate::types::*;

pub const SPCI_VERSION_MAJOR: i32 = 0x0;
pub const SPCI_VERSION_MINOR: i32 = 0x9;
pub const SPCI_VERSION_MAJOR_OFFSET: usize = 16;

/// Return type of SPCI functions.
/// TODO: Reuse `SpciReturn` type on all SPCI functions declarations.
#[repr(i32)]
#[derive(Clone, Copy, PartialEq)]
pub enum SpciReturn {
    Success = 0,
    NotSupported = -1,
    InvalidParameters = -2,
    NoMemory = -3,
    Busy = -4,
    Interrupted = -5,
    Denied = -6,
    Retry = -7,
}

/// Architected memory sharing message IDs.
#[repr(u16)]
#[derive(Clone, Copy, PartialEq)]
pub enum SpciMemoryShare {
    Donate = 0x2,
}

// SPCI function specific constants.
bitflags! {
    /// For SpciMessage::flags
    /// flags[15:1] reserved(MBZ).
    #[repr(C)]
    pub struct SpciMessageFlags: u16 {
        /// Architected message payload.
        const ARCHITECTED = 0b0000;

        /// Implementation defined message payload.
        const IMPDEF = 0b0001;
    }
}

bitflags! {
    pub struct SpciMsgRecvAttributes: u32 {
        const BLOCK = 0b0001;
    }
}

bitflags! {
    pub struct SpciMsgSendAttributes: u32 {
        const NOTIFY = 0b0001;
    }
}

/// The maximum length possible for a single message.
pub const SPCI_MSG_PAYLOAD_MAX: usize = HF_MAILBOX_SIZE - mem::size_of::<SpciMessage>();

/// SPCI common message header.
#[repr(C)]
#[derive(Clone)]
pub struct SpciMessage {
    // TODO: version is part of SPCI alpha2 but will be
    // removed in the next spec revision hence we are not
    // including it in the header.
    pub flags: SpciMessageFlags,

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
    /// `payload: [u8; 0]` makes any reference (even raw pointer) of SpciMessage
    /// being fat.
    /// Thus, don't make a variable with type `SpciMessage`. Usually that'll be
    /// not compatitable with `struct spci_message`.
    /// TODO: is here right place to use `Phantomdata`?
    pub payload: [u8; 0],
}

impl TryFrom<usize> for SpciMemoryShare {
    type Error = ();

    #[inline]
    fn try_from(from: usize) -> Result<Self, ()> {
        match from {
            0x2 => Ok(Self::Donate),
            _ => Err(()),
        }
    }
}

impl SpciMessage {
    /// Obtain a pointer to the architected header in the spci_message.
    ///
    /// Note: the argument "message" has const qualifier. This qualifier is meant to forbid changes
    /// in information enclosed in the struct SpciMessage. The SpciArchitectedMessageHeader, for
    /// which a pointer is returned in this function, is not part of SpciMessage. Its information is
    /// meant to be changed and hence the returned pointer does not have const type qualifier.
    #[inline]
    pub fn get_architected_message_header(&self) -> &SpciArchitectedMessageHeader {
        unsafe { &*(self.payload.as_ptr() as *const _) }
    }
}

#[repr(C)]
pub struct SpciArchitectedMessageHeader {
    pub r#type: SpciMemoryShare,

    // TODO: Padding is present to ensure that the field payload is aligned on
    // a 64B boundary. SPCI spec must be updated to reflect this.
    reserved: [u16; 3],
    pub payload: [u8; 0],
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
    pub count: u32,
    pub constituents: [SpciMemoryRegionConstituent; 0],
}

pub struct SpciMemTransitions {
    pub orig_from_mode: Mode,
    pub orig_to_mode: Mode,
    pub from_mode: Mode,
    pub to_mode: Mode,
}
