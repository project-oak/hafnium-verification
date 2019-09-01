/*
 * Copyright 2019 Jeehoon Kang.
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

use core::mem::{self, ManuallyDrop};
use core::ptr;

use crate::addr::*;
use crate::api::*;
use crate::mm::*;
use crate::page::*;
use crate::spci::*;
use crate::std::*;
use crate::vm::*;

/// Check if the message length and the number of memory region constituents match, if the check is
/// correct call the memory sharing routine.
fn spci_validate_call_share_memory(
    to_locked: ManuallyDrop<VmLocked>,
    from_locked: ManuallyDrop<VmLocked>,
    memory_region: &SpciMemoryRegion,
    memory_share_size: usize,
    memory_to_attributes: Mode,
    share: SpciMemoryShare,
) -> SpciReturn {
    let max_count = memory_region.count as usize;

    // Ensure the number of constituents are within the memory bounds.
    if memory_share_size
        != mem::size_of::<SpciMemoryRegion>()
            + mem::size_of::<SpciMemoryRegionConstituent>() * max_count
    {
        return SpciReturn::InvalidParameters;
    }

    unsafe {
        api_spci_share_memory(
            to_locked,
            from_locked,
            memory_region,
            memory_to_attributes.bits(),
            share as usize,
        )
    }
}

/// Performs initial architected message information parsing. Calls the corresponding api functions
/// implementing the functionality requested in the architected message.
pub fn spci_msg_handle_architected_message(
    to_locked: ManuallyDrop<VmLocked>,
    from_locked: ManuallyDrop<VmLocked>,
    architected_message_replica: &SpciArchitectedMessageHeader,
    from_msg_replica: &SpciMessage,
    to_msg: &mut SpciMessage,
) -> SpciReturn {
    // int64_t ret;
    let from_msg_payload_length = from_msg_replica.length as usize;

    let message_type = (*architected_message_replica).r#type;
    let ret = match message_type {
        SpciMemoryShare::Donate => {
            let memory_region = unsafe {
                &*((*architected_message_replica).payload.as_ptr() as *const SpciMemoryRegion)
            };
            let memory_share_size =
                from_msg_payload_length - mem::size_of::<SpciArchitectedMessageHeader>();
            // TODO: Add memory attributes.
            let to_mode = Mode::R | Mode::W | Mode::X;

            spci_validate_call_share_memory(
                to_locked,
                from_locked,
                memory_region,
                memory_share_size,
                to_mode,
                message_type,
            )
        }
        _ => {
            dlog!("Invalid memory sharing message.");
            return SpciReturn::InvalidParameters;
        }
    };

    // Copy data to the destination Rx.
    //
    // TODO: Translate the <from> IPA addresses to <to> IPA addresses.  Currently we assume identity
    // mapping of the stage 2 translation.  Removing this assumption relies on a mechanism to handle
    // scenarios where the memory region fits in the source Tx buffer but cannot fit in the
    // destination Rx buffer. This mechanism will be defined at the spec level.
    if ret == SpciReturn::Success {
        assert!(from_msg_payload_length <= SPCI_MSG_PAYLOAD_MAX);
        unsafe {
            ptr::copy_nonoverlapping(
                architected_message_replica,
                (*to_msg).payload.as_mut_ptr() as *mut _,
                from_msg_payload_length,
            );
        }
    }
    unsafe {
        ptr::write(to_msg, from_msg_replica.clone());
    }

    ret
}

/// Obtain the next mode to apply to the two VMs.
///
/// # Returns
///
/// The error code -1 indicates that a state transition was not found.  Success is indicated by 0.
fn spci_msg_get_next_state(
    transitions: &[SpciMemTransitions],
    memory_to_attributes: Mode,
    orig_from_mode: Mode,
    orig_to_mode: Mode,
    from_mode: &mut Mode,
    to_mode: &mut Mode,
) -> bool {
    let state_mask = Mode::INVALID | Mode::UNOWNED | Mode::SHARED;
    let orig_from_state = orig_from_mode & state_mask;
    let orig_to_state = orig_to_mode & state_mask;

    for transition in transitions {
        let table_orig_from_mode = transition.orig_from_mode;
        let table_orig_to_mode = transition.orig_to_mode;

        if orig_from_state == table_orig_from_mode && orig_to_state == table_orig_to_mode {
            *to_mode = transition.to_mode | memory_to_attributes;
            // TODO: Change access permission assignment to cater for the lend case.
            *from_mode = transition.from_mode;

            return true;
        }
    }
    false
}

/// Verify that all pages have the same mode, that the starting mode constitutes a valid state and
/// obtain the next mode to apply to the two VMs.
///
/// # Return
///
/// The error code false indicates that:
///  1) a state transition was not found;
///  2) the pages being shared do not have the same mode within the <to>
///    or <form> VMs;
///  3) The beginning and end IPAs are not page aligned;
///  4) The requested share type was not handled.
/// Success is indicated by true.
pub fn spci_msg_check_transition(
    to_locked: &ManuallyDrop<VmLocked>,
    from_locked: &ManuallyDrop<VmLocked>,
    share: SpciMemoryShare,
    orig_from_mode: &mut Mode,
    begin: ipaddr_t,
    end: ipaddr_t,
    memory_to_attributes: Mode,
    from_mode: &mut Mode,
    to_mode: &mut Mode,
) -> bool {
    // TODO: Transition table does not currently consider the multiple shared case.
    let donate_transitions: [SpciMemTransitions; 4] = [
        // 1) {O-EA, !O-NA} -> {!O-NA, O-EA}
        SpciMemTransitions {
            orig_from_mode: Mode::empty(),
            orig_to_mode: Mode::INVALID | Mode::UNOWNED,
            from_mode: Mode::INVALID | Mode::UNOWNED,
            to_mode: Mode::empty(),
        },
        // 2) {O-NA, !O-EA} -> {!O-NA, O-EA}
        SpciMemTransitions {
            orig_from_mode: Mode::INVALID,
            orig_to_mode: Mode::UNOWNED,
            from_mode: Mode::INVALID | Mode::UNOWNED,
            to_mode: Mode::empty(),
        },
        // 3) {O-SA, !O-SA} -> {!O-NA, O-EA}
        SpciMemTransitions {
            orig_from_mode: Mode::SHARED,
            orig_to_mode: Mode::UNOWNED | Mode::SHARED,
            from_mode: Mode::INVALID | Mode::UNOWNED,
            to_mode: Mode::empty(),
        },
        // Duplicate of 1) in order to cater for an alternative
        // representation of !O-NA:
        // (INVALID | UNOWNED | SHARED) and (INVALID | UNOWNED)
        // are both alternate representations of !O-NA.
        // 4) {O-EA, !O-NA} -> {!O-NA, O-EA}
        SpciMemTransitions {
            orig_from_mode: Mode::empty(),
            orig_to_mode: Mode::INVALID | Mode::UNOWNED | Mode::SHARED,
            from_mode: Mode::INVALID | Mode::UNOWNED | Mode::SHARED,
            to_mode: Mode::empty(),
        },
    ];

    // Fail if addresses are not page-aligned.
    if !is_aligned(ipa_addr(begin), PAGE_SIZE) || !is_aligned(ipa_addr(end), PAGE_SIZE) {
        return false;
    }

    // Ensure that the memory range is mapped with the same mode.
    *orig_from_mode = ok_or_return!(from_locked.get_inner().ptable.get_mode(begin, end), false);
    let orig_to_mode = ok_or_return!(to_locked.get_inner().ptable.get_mode(begin, end), false);

    if share != SpciMemoryShare::Donate {
        return false;
    }

    spci_msg_get_next_state(
        &donate_transitions,
        memory_to_attributes,
        *orig_from_mode,
        orig_to_mode,
        from_mode,
        to_mode,
    )
}
