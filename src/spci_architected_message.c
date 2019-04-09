/*
 * Copyright 2019 The Hafnium Authors.
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

#include "hf/api.h"
#include "hf/dlog.h"
#include "hf/spci_internal.h"
#include "hf/std.h"

/**
 * Check if the message length and the number of memory region constituents
 * match, if the check is correct call the memory sharing routine.
 */
static spci_return_t spci_validate_call_share_memory(
	struct vm_locked to_locked, struct vm_locked from_locked,
	struct spci_memory_region *memory_region, uint32_t memory_share_size,
	uint32_t memory_to_attributes, enum spci_memory_share share)
{
	uint32_t max_count = memory_region->count;

	/*
	 * Ensure the number of constituents are within the memory
	 * bounds.
	 */
	if (memory_share_size !=
	    sizeof(struct spci_memory_region) +
		    (sizeof(struct spci_memory_region_constituent) *
		     max_count)) {
		return SPCI_INVALID_PARAMETERS;
	}

	return api_spci_share_memory(to_locked, from_locked, memory_region,
				     memory_to_attributes, share);
}

/**
 * Performs initial architected message information parsing. Calls the
 * corresponding api functions implementing the functionality requested
 * in the architected message.
 */
spci_return_t spci_msg_handle_architected_message(
	struct vm_locked to_locked, struct vm_locked from_locked,
	const struct spci_architected_message_header
		*architected_message_replica,
	struct spci_message *from_msg_replica, struct spci_message *to_msg)
{
	int64_t ret;
	struct spci_memory_region *memory_region;
	uint32_t to_mode;
	uint32_t message_type;
	uint32_t memory_share_size;

	message_type = architected_message_replica->type;

	switch (message_type) {
	case SPCI_MEMORY_DONATE:
		memory_region = (struct spci_memory_region *)
					architected_message_replica->payload;

		memory_share_size =
			from_msg_replica->length -
			sizeof(struct spci_architected_message_header);

		/* TODO: Add memory attributes. */
		to_mode = MM_MODE_R | MM_MODE_W | MM_MODE_X;

		ret = spci_validate_call_share_memory(
			to_locked, from_locked, memory_region,
			memory_share_size, to_mode, message_type);
		break;

	default:
		dlog("Invalid memory sharing message.\n");
		return SPCI_INVALID_PARAMETERS;
	}

	/* Copy data to the destination Rx. */
	/*
	 * TODO: Translate the <from> IPA addresses to <to> IPA addresses.
	 * Currently we assume identity mapping of the stage 2 translation.
	 * Removing this assumption relies on a mechanism to handle scenarios
	 * where the memory region fits in the source Tx buffer but cannot fit
	 * in the destination Rx buffer. This mechanism will be defined at the
	 * spec level.
	 */
	if (ret == SPCI_SUCCESS) {
		memcpy_s(to_msg->payload, SPCI_MSG_PAYLOAD_MAX,
			 architected_message_replica, from_msg_replica->length);
	}
	*to_msg = *from_msg_replica;

	return ret;
}

/**
 * Obtain the next mode to apply to the two VMs.
 *
 * Returns:
 *  The error code -1 indicates that a state transition was not found.
 *  Success is indicated by 0.
 */
static bool spci_msg_get_next_state(
	const struct spci_mem_transitions *transitions,
	uint32_t transition_count, uint32_t memory_to_attributes,
	int orig_from_mode, int orig_to_mode, int *from_mode, int *to_mode)
{
	const uint32_t state_mask =
		MM_MODE_INVALID | MM_MODE_UNOWNED | MM_MODE_SHARED;
	const uint32_t orig_from_state = orig_from_mode & state_mask;

	for (uint32_t index = 0; index < transition_count; index++) {
		uint32_t table_orig_from_mode =
			transitions[index].orig_from_mode;
		uint32_t table_orig_to_mode = transitions[index].orig_to_mode;

		if (((orig_from_state) == table_orig_from_mode) &&
		    ((orig_to_mode & state_mask) == table_orig_to_mode)) {
			*to_mode = transitions[index].to_mode |
				   memory_to_attributes;
			/*
			 * TODO: Change access permission assignment to cater
			 * for the lend case.
			 */
			*from_mode = transitions[index].from_mode;

			return true;
		}
	}
	return false;
}

/**
 * Verify that all pages have the same mode, that the starting mode
 * constitutes a valid state and obtain the next mode to apply
 * to the two VMs.
 *
 * Returns:
 *  The error code false indicates that:
 *   1) a state transition was not found;
 *   2) the pages being shared do not have the same mode within the <to>
 *     or <form> VMs;
 *   3) The beginning and end IPAs are not page aligned;
 *   4) The requested share type was not handled.
 *  Success is indicated by true.
 *
 */
bool spci_msg_check_transition(struct vm *to, struct vm *from,
			       enum spci_memory_share share,
			       int *orig_from_mode, ipaddr_t begin,
			       ipaddr_t end, uint32_t memory_to_attributes,
			       int *from_mode, int *to_mode)
{
	int orig_to_mode;
	const struct spci_mem_transitions *mem_transition_table;
	uint32_t transition_table_size;

	/*
	 * TODO: Transition table does not currently consider the multiple
	 * shared case.
	 */
	static const struct spci_mem_transitions donate_transitions[] = {
		{
			/* 1) {O-EA, !O-NA} -> {!O-NA, O-EA} */
			.orig_from_mode = 0,
			.orig_to_mode = MM_MODE_INVALID | MM_MODE_UNOWNED,
			.from_mode = MM_MODE_INVALID | MM_MODE_UNOWNED,
			.to_mode = 0,
		},
		{
			/* 2) {O-NA, !O-EA} -> {!O-NA, O-EA} */
			.orig_from_mode = MM_MODE_INVALID,
			.orig_to_mode = MM_MODE_UNOWNED,
			.from_mode = MM_MODE_INVALID | MM_MODE_UNOWNED,
			.to_mode = 0,
		},
		{
			/* 3) {O-SA, !O-SA} -> {!O-NA, O-EA} */
			.orig_from_mode = MM_MODE_SHARED,
			.orig_to_mode = MM_MODE_UNOWNED | MM_MODE_SHARED,
			.from_mode = MM_MODE_INVALID | MM_MODE_UNOWNED,
			.to_mode = 0,
		},
		{
			/*
			 * Duplicate of 1) in order to cater for an alternative
			 * representation of !O-NA:
			 * (INVALID | UNOWNED | SHARED) and (INVALID | UNOWNED)
			 * are both alternate representations of !O-NA.
			 */
			/* 4) {O-EA, !O-NA} -> {!O-NA, O-EA} */
			.orig_from_mode = 0,
			.orig_to_mode = MM_MODE_INVALID | MM_MODE_UNOWNED |
					MM_MODE_SHARED,
			.from_mode = MM_MODE_INVALID | MM_MODE_UNOWNED |
				     MM_MODE_SHARED,
			.to_mode = 0,
		},
	};
	static const uint32_t size_donate_transitions =
		ARRAY_SIZE(donate_transitions);

	/* Fail if addresses are not page-aligned. */
	if (!is_aligned(ipa_addr(begin), PAGE_SIZE) ||
	    !is_aligned(ipa_addr(end), PAGE_SIZE)) {
		return false;
	}

	/*
	 * Ensure that the memory range is mapped with the same
	 * mode.
	 */
	if (!mm_vm_get_mode(&from->ptable, begin, end, orig_from_mode) ||
	    !mm_vm_get_mode(&to->ptable, begin, end, &orig_to_mode)) {
		return false;
	}

	switch (share) {
	case SPCI_MEMORY_DONATE:
		mem_transition_table = donate_transitions;
		transition_table_size = size_donate_transitions;
		break;

	default:
		return false;
	}

	return spci_msg_get_next_state(mem_transition_table,
				       transition_table_size,
				       memory_to_attributes, *orig_from_mode,
				       orig_to_mode, from_mode, to_mode);
}
