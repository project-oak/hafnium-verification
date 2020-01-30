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

#include "hf/spci.h"

#include "hf/types.h"

/*
 * Copied from hf/arch/std.h because we can't include Hafnium internal headers
 * here.
 */
#ifndef align_up
#define align_up(v, a) (((uintptr_t)(v) + ((a)-1)) & ~((a)-1))
#endif

/**
 * Initialises the given `spci_memory_region` and copies the constituent
 * information to it. Returns the length in bytes occupied by the data copied to
 * `memory_region` (attributes, constituents and memory region header size).
 */
uint32_t spci_memory_region_init(
	struct spci_memory_region *memory_region, spci_vm_id_t sender, spci_vm_id_t receiver,
	const struct spci_memory_region_constituent constituents[],
	uint32_t constituent_count, uint32_t tag, spci_memory_region_flags_t flags,
	enum spci_memory_access access, enum spci_memory_type type,
	enum spci_memory_cacheability cacheability,
	enum spci_memory_shareability shareability)
{
	uint32_t constituents_length =
		constituent_count *
		sizeof(struct spci_memory_region_constituent);
	uint32_t index;
	struct spci_memory_region_constituent *region_constituents;
	uint16_t attributes = 0;

	/* Set memory region's page attributes. */
	spci_set_memory_access_attr(&attributes, access);
	spci_set_memory_type_attr(&attributes, type);
	spci_set_memory_cacheability_attr(&attributes, cacheability);
	spci_set_memory_shareability_attr(&attributes, shareability);

	memory_region->tag = tag;
	memory_region->flags = flags;
	memory_region->sender = sender;
	memory_region->reserved = 0;
	memory_region->page_count = 0;
	memory_region->constituent_count = constituent_count;
	memory_region->attribute_count = 1;
	memory_region->attributes[0].receiver = receiver;
	memory_region->attributes[0].memory_attributes = attributes;

	/*
	 * Constituent offset must be aligned to a 64-bit boundary so that
	 * 64-bit addresses can be copied without alignment faults.
	 */
	memory_region->constituent_offset = align_up(
		sizeof(struct spci_memory_region) +
			memory_region->attribute_count *
				sizeof(struct spci_memory_region_attributes),
		8);
	region_constituents =
		spci_memory_region_get_constituents(memory_region);

	for (index = 0; index < constituent_count; index++) {
		region_constituents[index] = constituents[index];
		region_constituents[index].reserved = 0;
		memory_region->page_count += constituents[index].page_count;
	}

	/*
	 * TODO: Add assert ensuring that the specified message
	 * length is not greater than SPCI_MSG_PAYLOAD_MAX.
	 */

	return memory_region->constituent_offset + constituents_length;
}
