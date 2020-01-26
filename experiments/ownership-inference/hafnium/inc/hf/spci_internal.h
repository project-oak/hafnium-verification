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

#pragma once

#include "hf/addr.h"
#include "hf/vm.h"

#include "vmapi/hf/spci.h"

#define SPCI_VERSION_MAJOR 0x0
#define SPCI_VERSION_MINOR 0x9

#define SPCI_VERSION_MAJOR_OFFSET 16

struct spci_mem_transitions {
	uint32_t orig_from_mode;
	uint32_t orig_to_mode;
	uint32_t from_mode;
	uint32_t to_mode;
};

/* TODO: Add device attributes: GRE, cacheability, shareability. */
static inline uint32_t spci_memory_attrs_to_mode(uint16_t memory_attributes)
{
	uint32_t mode = 0;

	switch (spci_get_memory_access_attr(memory_attributes)) {
	case SPCI_MEMORY_RO_NX:
		mode = MM_MODE_R;
		break;
	case SPCI_MEMORY_RO_X:
		mode = MM_MODE_R | MM_MODE_X;
		break;
	case SPCI_MEMORY_RW_NX:
		mode = MM_MODE_R | MM_MODE_W;
		break;
	case SPCI_MEMORY_RW_X:
		mode = MM_MODE_R | MM_MODE_W | MM_MODE_X;
		break;
	}

	return mode;
}

static inline struct spci_value spci_error(uint64_t error_code)
{
	return (struct spci_value){.func = SPCI_ERROR_32, .arg2 = error_code};
}

struct spci_value spci_msg_handle_architected_message(
	struct vm_locked to_locked, struct vm_locked from_locked,
	struct spci_memory_region *memory_region, uint32_t size,
	uint32_t share_func, struct mpool *api_page_pool);
