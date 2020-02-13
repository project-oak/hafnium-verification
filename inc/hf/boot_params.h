/*
 * Copyright 2018 The Hafnium Authors.
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

#include <stdbool.h>

#include "hf/arch/cpu.h"

#include "hf/fdt.h"
#include "hf/mm.h"
#include "hf/mpool.h"

#define MAX_MEM_RANGES 20

struct mem_range {
	paddr_t begin;
	paddr_t end;
};

struct boot_params {
	cpu_id_t cpu_ids[MAX_CPUS];
	size_t cpu_count;
	struct mem_range mem_ranges[MAX_MEM_RANGES];
	size_t mem_ranges_count;
	paddr_t initrd_begin;
	paddr_t initrd_end;
	uintreg_t kernel_arg;
};

struct boot_params_update {
	struct mem_range reserved_ranges[MAX_MEM_RANGES];
	size_t reserved_ranges_count;
	paddr_t initrd_begin;
	paddr_t initrd_end;
};

bool boot_params_init(struct boot_params *p, const struct fdt_node *fdt_root);
bool boot_params_patch_fdt(struct mm_stage1_locked stage1_locked,
			   struct boot_params_update *p, struct mpool *ppool);
