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

#include "hf/boot_params.h"
#include "hf/fdt.h"
#include "hf/mm.h"
#include "hf/mpool.h"

struct fdt_header *fdt_map(struct mm_stage1_locked stage1_locked,
			   paddr_t fdt_addr, struct fdt_node *n,
			   struct mpool *ppool);
bool fdt_unmap(struct mm_stage1_locked stage1_locked, struct fdt_header *fdt,
	       struct mpool *ppool);
void fdt_find_cpus(const struct fdt_node *root, uint64_t *cpu_ids,
		   size_t *cpu_count);
void fdt_find_memory_ranges(const struct fdt_node *root, struct boot_params *p);
bool fdt_find_initrd(struct fdt_node *n, paddr_t *begin, paddr_t *end);

/** Apply an update to the FDT. */
bool fdt_patch(struct mm_stage1_locked stage1_locked, paddr_t fdt_addr,
	       struct boot_params_update *p, struct mpool *ppool);
