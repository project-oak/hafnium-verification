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
#include "hf/check.h"
#include "hf/dlog.h"
#include "hf/spci_internal.h"
#include "hf/std.h"
#include "hf/vm.h"

/**
 * Obtain the next mode to apply to the two VMs.
 *
 * Returns true iff a state transition was found.
 */
static bool spci_msg_get_next_state(
	const struct spci_mem_transitions *transitions,
	uint32_t transition_count, uint32_t memory_to_attributes,
	uint32_t orig_from_mode, uint32_t orig_to_mode, uint32_t *from_mode,
	uint32_t *to_mode)
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

			*from_mode = transitions[index].from_mode |
				     (~state_mask & orig_from_mode);

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
static bool spci_msg_check_transition(struct vm *to, struct vm *from,
				      uint32_t share_func,
				      uint32_t *orig_from_mode,
				      struct spci_memory_region *memory_region,
				      uint32_t memory_to_attributes,
				      uint32_t *from_mode, uint32_t *to_mode)
{
	uint32_t orig_to_mode;
	const struct spci_mem_transitions *mem_transition_table;
	uint32_t transition_table_size;
	uint32_t i;

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

	/*
	 * This data structure holds the allowed state transitions for the
	 * "lend" state machine. In this state machine the owner keeps ownership
	 * but loses access to the lent pages.
	 */
	static const struct spci_mem_transitions lend_transitions[] = {
		{
			/* 1) {O-EA, !O-NA} -> {O-NA, !O-EA} */
			.orig_from_mode = 0,
			.orig_to_mode = MM_MODE_INVALID | MM_MODE_UNOWNED |
					MM_MODE_SHARED,
			.from_mode = MM_MODE_INVALID,
			.to_mode = MM_MODE_UNOWNED,
		},
		{
			/*
			 * Duplicate of 1) in order to cater for an alternative
			 * representation of !O-NA:
			 * (INVALID | UNOWNED | SHARED) and (INVALID | UNOWNED)
			 * are both alternate representations of !O-NA.
			 */
			/* 2) {O-EA, !O-NA} -> {O-NA, !O-EA} */
			.orig_from_mode = 0,
			.orig_to_mode = MM_MODE_INVALID | MM_MODE_UNOWNED,
			.from_mode = MM_MODE_INVALID,
			.to_mode = MM_MODE_UNOWNED,
		},
	};

	static const uint32_t size_lend_transitions =
		ARRAY_SIZE(lend_transitions);

	/*
	 * This data structure holds the allowed state transitions for the
	 * "share" state machine. In this state machine the owner keeps the
	 * shared pages mapped on its stage2 table and keeps access as well.
	 */
	static const struct spci_mem_transitions share_transitions[] = {
		{
			/* 1) {O-EA, !O-NA} -> {O-SA, !O-SA} */
			.orig_from_mode = 0,
			.orig_to_mode = MM_MODE_INVALID | MM_MODE_UNOWNED |
					MM_MODE_SHARED,
			.from_mode = MM_MODE_SHARED,
			.to_mode = MM_MODE_UNOWNED | MM_MODE_SHARED,
		},
		{
			/*
			 * Duplicate of 1) in order to cater for an alternative
			 * representation of !O-NA:
			 * (INVALID | UNOWNED | SHARED) and (INVALID | UNOWNED)
			 * are both alternate representations of !O-NA.
			 */
			/* 2) {O-EA, !O-NA} -> {O-SA, !O-SA} */
			.orig_from_mode = 0,
			.orig_to_mode = MM_MODE_INVALID | MM_MODE_UNOWNED,
			.from_mode = MM_MODE_SHARED,
			.to_mode = MM_MODE_UNOWNED | MM_MODE_SHARED,
		},
	};

	static const uint32_t size_share_transitions =
		ARRAY_SIZE(share_transitions);

	static const struct spci_mem_transitions relinquish_transitions[] = {
		{
			/* 1) {!O-EA, O-NA} -> {!O-NA, O-EA} */
			.orig_from_mode = MM_MODE_UNOWNED,
			.orig_to_mode = MM_MODE_INVALID,
			.from_mode = MM_MODE_INVALID | MM_MODE_UNOWNED |
				     MM_MODE_SHARED,
			.to_mode = 0,
		},
		{
			/* 2) {!O-SA, O-SA} -> {!O-NA, O-EA} */
			.orig_from_mode = MM_MODE_UNOWNED | MM_MODE_SHARED,
			.orig_to_mode = MM_MODE_SHARED,
			.from_mode = MM_MODE_INVALID | MM_MODE_UNOWNED |
				     MM_MODE_SHARED,
			.to_mode = 0,
		},
	};

	static const uint32_t size_relinquish_transitions =
		ARRAY_SIZE(relinquish_transitions);

	struct spci_memory_region_constituent *constituents =
		spci_memory_region_get_constituents(memory_region);

	if (memory_region->constituent_count == 0) {
		/*
		 * Fail if there are no constituents. Otherwise
		 * spci_msg_get_next_state would get an unitialised
		 * *orig_from_mode and orig_to_mode.
		 */
		return false;
	}

	for (i = 0; i < memory_region->constituent_count; ++i) {
		ipaddr_t begin = ipa_init(constituents[i].address);
		size_t size = constituents[i].page_count * PAGE_SIZE;
		ipaddr_t end = ipa_add(begin, size);
		uint32_t current_from_mode;
		uint32_t current_to_mode;

		/* Fail if addresses are not page-aligned. */
		if (!is_aligned(ipa_addr(begin), PAGE_SIZE) ||
		    !is_aligned(ipa_addr(end), PAGE_SIZE)) {
			return false;
		}

		/*
		 * Ensure that this constituent memory range is all mapped with
		 * the same mode.
		 */
		if (!mm_vm_get_mode(&from->ptable, begin, end,
				    &current_from_mode) ||
		    !mm_vm_get_mode(&to->ptable, begin, end,
				    &current_to_mode)) {
			return false;
		}

		/*
		 * Ensure that all constituents are mapped with the same mode.
		 */
		if (i == 0) {
			*orig_from_mode = current_from_mode;
			orig_to_mode = current_to_mode;
		} else if (current_from_mode != *orig_from_mode ||
			   current_to_mode != orig_to_mode) {
			return false;
		}
	}

	/* Ensure the address range is normal memory and not a device. */
	if (*orig_from_mode & MM_MODE_D) {
		return false;
	}

	switch (share_func) {
	case SPCI_MEM_DONATE_32:
		mem_transition_table = donate_transitions;
		transition_table_size = size_donate_transitions;
		break;

	case SPCI_MEM_LEND_32:
		mem_transition_table = lend_transitions;
		transition_table_size = size_lend_transitions;
		break;

	case SPCI_MEM_SHARE_32:
		mem_transition_table = share_transitions;
		transition_table_size = size_share_transitions;
		break;

	case HF_SPCI_MEM_RELINQUISH:
		mem_transition_table = relinquish_transitions;
		transition_table_size = size_relinquish_transitions;
		break;

	default:
		return false;
	}

	return spci_msg_get_next_state(mem_transition_table,
				       transition_table_size,
				       memory_to_attributes, *orig_from_mode,
				       orig_to_mode, from_mode, to_mode);
}

/**
 * Updates a VM's page table such that the given set of physical address ranges
 * are mapped in the address space at the corresponding address ranges, in the
 * mode provided.
 *
 * If commit is false, the page tables will be allocated from the mpool but no
 * mappings will actually be updated. This function must always be called first
 * with commit false to check that it will succeed before calling with commit
 * true, to avoid leaving the page table in a half-updated state. To make a
 * series of changes atomically you can call them all with commit false before
 * calling them all with commit true.
 *
 * mm_vm_defrag should always be called after a series of page table updates,
 * whether they succeed or fail.
 *
 * Returns true on success, or false if the update failed and no changes were
 * made to memory mappings.
 */
static bool spci_region_group_identity_map(
	struct vm_locked vm_locked, struct spci_memory_region *memory_region,
	int mode, struct mpool *ppool, bool commit)
{
	struct spci_memory_region_constituent *constituents =
		spci_memory_region_get_constituents(memory_region);
	uint32_t memory_constituent_count = memory_region->constituent_count;

	/* Iterate over the memory region constituents. */
	for (uint32_t index = 0; index < memory_constituent_count; index++) {
		size_t size = constituents[index].page_count * PAGE_SIZE;
		paddr_t pa_begin =
			pa_from_ipa(ipa_init(constituents[index].address));
		paddr_t pa_end = pa_add(pa_begin, size);

		if (commit) {
			vm_identity_commit(vm_locked, pa_begin, pa_end, mode,
					   ppool, NULL);
		} else if (!vm_identity_prepare(vm_locked, pa_begin, pa_end,
						mode, ppool)) {
			return false;
		}
	}

	return true;
}

/**
 * Clears a region of physical memory by overwriting it with zeros. The data is
 * flushed from the cache so the memory has been cleared across the system.
 */
static bool clear_memory(paddr_t begin, paddr_t end, struct mpool *ppool)
{
	/*
	 * TODO: change this to a CPU local single page window rather than a
	 *       global mapping of the whole range. Such an approach will limit
	 *       the changes to stage-1 tables and will allow only local
	 *       invalidation.
	 */
	bool ret;
	struct mm_stage1_locked stage1_locked = mm_lock_stage1();
	void *ptr =
		mm_identity_map(stage1_locked, begin, end, MM_MODE_W, ppool);
	size_t size = pa_difference(begin, end);

	if (!ptr) {
		/* TODO: partial defrag of failed range. */
		/* Recover any memory consumed in failed mapping. */
		mm_defrag(stage1_locked, ppool);
		goto fail;
	}

	memset_s(ptr, size, 0, size);
	arch_mm_flush_dcache(ptr, size);
	mm_unmap(stage1_locked, begin, end, ppool);

	ret = true;
	goto out;

fail:
	ret = false;

out:
	mm_unlock_stage1(&stage1_locked);

	return ret;
}

/**
 * Clears a region of physical memory by overwriting it with zeros. The data is
 * flushed from the cache so the memory has been cleared across the system.
 */
static bool spci_clear_memory_region(struct spci_memory_region *memory_region,
				     struct mpool *api_page_pool)
{
	struct mpool local_page_pool;
	struct spci_memory_region_constituent *constituents =
		spci_memory_region_get_constituents(memory_region);
	uint32_t memory_constituent_count = memory_region->constituent_count;
	struct mm_stage1_locked stage1_locked;
	bool ret = false;

	/*
	 * Create a local pool so any freed memory can't be used by another
	 * thread. This is to ensure each constituent that is mapped can be
	 * unmapped again afterwards.
	 */
	mpool_init_with_fallback(&local_page_pool, api_page_pool);

	/* Iterate over the memory region constituents. */
	for (uint32_t i = 0; i < memory_constituent_count; ++i) {
		size_t size = constituents[i].page_count * PAGE_SIZE;
		paddr_t begin = pa_from_ipa(ipa_init(constituents[i].address));
		paddr_t end = pa_add(begin, size);

		if (!clear_memory(begin, end, &local_page_pool)) {
			/*
			 * api_clear_memory will defrag on failure, so no need
			 * to do it here.
			 */
			goto out;
		}
	}

	/*
	 * Need to defrag after clearing, as it may have added extra mappings to
	 * the stage 1 page table.
	 */
	stage1_locked = mm_lock_stage1();
	mm_defrag(stage1_locked, &local_page_pool);
	mm_unlock_stage1(&stage1_locked);

	ret = true;

out:
	mpool_fini(&local_page_pool);
	return ret;
}

/**
 * Shares memory from the calling VM with another. The memory can be shared in
 * different modes.
 *
 * This function requires the calling context to hold the <to> and <from> locks.
 *
 * Returns:
 *  In case of error one of the following values is returned:
 *   1) SPCI_INVALID_PARAMETERS - The endpoint provided parameters were
 *     erroneous;
 *   2) SPCI_NO_MEMORY - Hafnium did not have sufficient memory to complete
 *     the request.
 *  Success is indicated by SPCI_SUCCESS.
 */
static struct spci_value spci_share_memory(
	struct vm_locked to_locked, struct vm_locked from_locked,
	struct spci_memory_region *memory_region, uint32_t memory_to_attributes,
	uint32_t share_func, struct mpool *api_page_pool)
{
	struct vm *to = to_locked.vm;
	struct vm *from = from_locked.vm;
	uint32_t orig_from_mode;
	uint32_t from_mode;
	uint32_t to_mode;
	struct mpool local_page_pool;
	struct spci_value ret;
	struct spci_memory_region_constituent *constituents =
		spci_memory_region_get_constituents(memory_region);

	/*
	 * Make sure constituents are properly aligned to a 64-bit boundary. If
	 * not we would get alignment faults trying to read (64-bit) page
	 * addresses.
	 */
	if (!is_aligned(constituents, 8)) {
		return spci_error(SPCI_INVALID_PARAMETERS);
	}

	/* Disallow reflexive shares as this suggests an error in the VM. */
	if (to == from) {
		return spci_error(SPCI_INVALID_PARAMETERS);
	}

	/*
	 * Check if the state transition is lawful for both VMs involved
	 * in the memory exchange, ensure that all constituents of a memory
	 * region being shared are at the same state.
	 */
	if (!spci_msg_check_transition(to, from, share_func, &orig_from_mode,
				       memory_region, memory_to_attributes,
				       &from_mode, &to_mode)) {
		return spci_error(SPCI_INVALID_PARAMETERS);
	}

	/*
	 * Create a local pool so any freed memory can't be used by another
	 * thread. This is to ensure the original mapping can be restored if the
	 * clear fails.
	 */
	mpool_init_with_fallback(&local_page_pool, api_page_pool);

	/*
	 * First reserve all required memory for the new page table entries in
	 * both sender and recipient page tables without committing, to make
	 * sure the entire operation will succeed without exhausting the page
	 * pool.
	 */
	if (!spci_region_group_identity_map(from_locked, memory_region,
					    from_mode, api_page_pool, false) ||
	    !spci_region_group_identity_map(to_locked, memory_region, to_mode,
					    api_page_pool, false)) {
		/* TODO: partial defrag of failed range. */
		ret = spci_error(SPCI_NO_MEMORY);
		goto out;
	}

	/*
	 * First update the mapping for the sender so there is no overlap with
	 * the recipient. This won't allocate because the transaction was
	 * already prepared above, but may free pages in the case that a whole
	 * block is being unmapped that was previously partially mapped.
	 */
	CHECK(spci_region_group_identity_map(
		from_locked, memory_region, from_mode, &local_page_pool, true));

	/* Clear the memory so no VM or device can see the previous contents. */
	if ((memory_region->flags & SPCI_MEMORY_REGION_FLAG_CLEAR) &&
	    !spci_clear_memory_region(memory_region, api_page_pool)) {
		/*
		 * On failure, roll back by returning memory to the sender. This
		 * may allocate pages which were previously freed into
		 * `local_page_pool` by the call above, but will never allocate
		 * more pages than that so can never fail.
		 */
		CHECK(spci_region_group_identity_map(from_locked, memory_region,
						     orig_from_mode,
						     &local_page_pool, true));

		ret = spci_error(SPCI_NO_MEMORY);
		goto out;
	}

	/*
	 * Complete the transfer by mapping the memory into the recipient. This
	 * won't allocate because the transaction was already prepared above, so
	 * it doesn't need to use the `local_page_pool`.
	 */
	CHECK(spci_region_group_identity_map(to_locked, memory_region, to_mode,
					     api_page_pool, true));

	ret = (struct spci_value){.func = SPCI_SUCCESS_32};

out:
	mpool_fini(&local_page_pool);

	/*
	 * Tidy up the page tables by reclaiming failed mappings (if there was
	 * an error) or merging entries into blocks where possible (on success).
	 */
	mm_vm_defrag(&to->ptable, api_page_pool);
	mm_vm_defrag(&from->ptable, api_page_pool);

	return ret;
}

/**
 * Check if the message length and the number of memory region constituents
 * match, if the check is correct call the memory sharing routine.
 */
static struct spci_value spci_validate_call_share_memory(
	struct vm_locked to_locked, struct vm_locked from_locked,
	struct spci_memory_region *memory_region, uint32_t memory_share_size,
	uint32_t share_func, struct mpool *api_page_pool)
{
	uint32_t memory_to_attributes;
	uint32_t attributes_size;
	uint32_t constituents_size;

	/*
	 * Ensure the number of constituents are within the memory
	 * bounds.
	 */
	attributes_size = sizeof(struct spci_memory_region_attributes) *
			  memory_region->attribute_count;
	constituents_size = sizeof(struct spci_memory_region_constituent) *
			    memory_region->constituent_count;
	if (memory_region->constituent_offset <
		    sizeof(struct spci_memory_region) + attributes_size ||
	    memory_share_size !=
		    memory_region->constituent_offset + constituents_size) {
		return spci_error(SPCI_INVALID_PARAMETERS);
	}

	/* The sender must match the message sender. */
	if (memory_region->sender != from_locked.vm->id) {
		return spci_error(SPCI_INVALID_PARAMETERS);
	}

	/* We only support a single recipient. */
	if (memory_region->attribute_count != 1) {
		return spci_error(SPCI_NOT_SUPPORTED);
	}

	/* The recipient must match the message recipient. */
	if (memory_region->attributes[0].receiver != to_locked.vm->id) {
		return spci_error(SPCI_INVALID_PARAMETERS);
	}

	switch (share_func) {
	case SPCI_MEM_DONATE_32:
	case SPCI_MEM_LEND_32:
	case SPCI_MEM_SHARE_32:
		memory_to_attributes = spci_memory_attrs_to_mode(
			memory_region->attributes[0].memory_attributes);
		break;
	case HF_SPCI_MEM_RELINQUISH:
		memory_to_attributes = MM_MODE_R | MM_MODE_W | MM_MODE_X;
		break;
	default:
		dlog("Invalid memory sharing message.\n");
		return spci_error(SPCI_INVALID_PARAMETERS);
	}

	return spci_share_memory(to_locked, from_locked, memory_region,
				 memory_to_attributes, share_func,
				 api_page_pool);
}

/**
 * Performs initial architected message information parsing. Calls the
 * corresponding api functions implementing the functionality requested
 * in the architected message.
 */
struct spci_value spci_msg_handle_architected_message(
	struct vm_locked to_locked, struct vm_locked from_locked,
	struct spci_memory_region *memory_region, uint32_t size,
	uint32_t share_func, struct mpool *api_page_pool)
{
	struct spci_value ret = spci_validate_call_share_memory(
		to_locked, from_locked, memory_region, size, share_func,
		api_page_pool);

	/* Copy data to the destination Rx. */
	/*
	 * TODO: Translate the <from> IPA addresses to <to> IPA addresses.
	 * Currently we assume identity mapping of the stage 2 translation.
	 * Removing this assumption relies on a mechanism to handle scenarios
	 * where the memory region fits in the source Tx buffer but cannot fit
	 * in the destination Rx buffer. This mechanism will be defined at the
	 * spec level.
	 */
	if (ret.func == SPCI_SUCCESS_32) {
		memcpy_s(to_locked.vm->mailbox.recv, SPCI_MSG_PAYLOAD_MAX,
			 memory_region, size);
		to_locked.vm->mailbox.recv_size = size;
		to_locked.vm->mailbox.recv_sender = from_locked.vm->id;
		to_locked.vm->mailbox.recv_func = share_func;
	}

	return ret;
}
