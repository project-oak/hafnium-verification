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

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>

#include "hf/arch/mm.h"

#include "hf/addr.h"
#include "hf/assert.h"
#include "hf/mpool.h"

/* Keep macro alignment */
/* clang-format off */

#define PAGE_SIZE (1 << PAGE_BITS)
#define MM_PTE_PER_PAGE (PAGE_SIZE / sizeof(pte_t))


/* The following are arch-independent page mapping modes. */
#define MM_MODE_R 0x0001 /* read */
#define MM_MODE_W 0x0002 /* write */
#define MM_MODE_X 0x0004 /* execute */
#define MM_MODE_D 0x0008 /* device */

/*
 * Memory in stage-1 is either valid (present) or invalid (absent).
 *
 * Memory in stage-2 has more states to track sharing, borrowing and giving of
 * memory. The states are made up of three parts:
 *
 *  1. V = valid/invalid    : Whether the memory is part of the VM's address
 *                            space. A fault will be generated if accessed when
 *                            invalid.
 *  2. O = owned/unowned    : Whether the memory is owned by the VM.
 *  3. X = exclusive/shared : Whether access is exclusive to the VM or shared
 *                            with at most one other.
 *
 * These parts compose to form the following state:
 *
 *  -  V  O  X : Owner of memory with exclusive access.
 *  -  V  O !X : Owner of memory with access shared with at most one other VM.
 *  -  V !O  X : Borrower of memory with exclusive access.
 *  -  V !O !X : Borrower of memory where access is shared with the owner.
 *  - !V  O  X : Owner of memory lent to a VM that has exclusive access.
 *
 *  - !V  O !X : Unused. Owner of shared memory always has access.
 *
 *  - !V !O  X : Invalid memory. Memory is unrelated to the VM.
 *  - !V !O !X : Invalid memory. Memory is unrelated to the VM.
 *
 *  Modes are selected so that owner of exclusive memory is the default.
 */
#define MM_MODE_INVALID 0x0010
#define MM_MODE_UNOWNED 0x0020
#define MM_MODE_SHARED  0x0040

/* clang-format on */

struct mm_page_table {
	alignas(PAGE_SIZE) pte_t entries[MM_PTE_PER_PAGE];
};
static_assert(sizeof(struct mm_page_table) == PAGE_SIZE,
	      "A page table must take exactly one page.");
static_assert(alignof(struct mm_page_table) == PAGE_SIZE,
	      "A page table must be page aligned.");

struct mm_ptable {
	/** Address of the root of the page table. */
	paddr_t root;
};

void mm_vm_enable_invalidation(void);

bool mm_vm_init(struct mm_ptable *t, struct mpool *ppool);
void mm_vm_fini(struct mm_ptable *t, struct mpool *ppool);
bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
			int mode, ipaddr_t *ipa, struct mpool *ppool);
bool mm_vm_unmap(struct mm_ptable *t, paddr_t begin, paddr_t end,
		 struct mpool *ppool);
bool mm_vm_unmap_hypervisor(struct mm_ptable *t, struct mpool *ppool);
void mm_vm_defrag(struct mm_ptable *t, struct mpool *ppool);
void mm_vm_dump(struct mm_ptable *t);
bool mm_vm_get_mode(struct mm_ptable *t, ipaddr_t begin, ipaddr_t end,
		    int *mode);

bool mm_init(struct mpool *ppool);
bool mm_cpu_init(void);
void *mm_identity_map(paddr_t begin, paddr_t end, int mode,
		      struct mpool *ppool);
bool mm_unmap(paddr_t begin, paddr_t end, struct mpool *ppool);
void mm_defrag(struct mpool *ppool);
