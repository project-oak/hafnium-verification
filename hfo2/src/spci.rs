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

use crate::types::*;

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
    flags: u16,

    /// TODO: Padding is present to ensure controlled offset
    /// of the length field. SPCI spec must be updated
    /// to reflect this (TBD).
    reserved_1: u16,

    length: u32,
    target_vm_id: spci_vm_id_t,
    source_vm_id: spci_vm_id_t,

    /// TODO: Padding is present to ensure that the field
    /// payload alignment is 64B. SPCI spec must be updated
    /// to reflect this.
    reserved_2: u32,

    payload: [u8],
}