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

#include "hf/fdt.h"
#include "hf/memiter.h"
#include "hf/spci.h"
#include "hf/string.h"
#include "hf/vm.h"

/**
 * Holds information about one of the VMs described in the manifest.
 */
struct manifest_vm {
	/* Properties defined for both primary and secondary VMs. */
	struct string debug_name;
	struct string kernel_filename;
	struct smc_whitelist smc_whitelist;

	union {
		/* Properties specific to the primary VM. */
		struct {
			struct string ramdisk_filename;
		} primary;
		/* Properties specific to secondary VMs. */
		struct {
			uint64_t mem_size;
			spci_vcpu_count_t vcpu_count;
		} secondary;
	};
};

/**
 * Hafnium manifest parsed from FDT.
 */
struct manifest {
	spci_vm_count_t vm_count;
	struct manifest_vm vm[MAX_VMS];
};

enum manifest_return_code {
	MANIFEST_SUCCESS = 0,
	MANIFEST_ERROR_NO_HYPERVISOR_FDT_NODE,
	MANIFEST_ERROR_NOT_COMPATIBLE,
	MANIFEST_ERROR_RESERVED_VM_ID,
	MANIFEST_ERROR_NO_PRIMARY_VM,
	MANIFEST_ERROR_TOO_MANY_VMS,
	MANIFEST_ERROR_PROPERTY_NOT_FOUND,
	MANIFEST_ERROR_MALFORMED_STRING,
	MANIFEST_ERROR_STRING_TOO_LONG,
	MANIFEST_ERROR_MALFORMED_STRING_LIST,
	MANIFEST_ERROR_MALFORMED_INTEGER,
	MANIFEST_ERROR_INTEGER_OVERFLOW,
	MANIFEST_ERROR_MALFORMED_INTEGER_LIST,
	MANIFEST_ERROR_MALFORMED_BOOLEAN,
};

enum manifest_return_code manifest_init(struct manifest *manifest,
					const struct fdt_node *fdt_root);

const char *manifest_strerror(enum manifest_return_code ret_code);
