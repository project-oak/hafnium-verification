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

#include "hf/arch/vm/mm.h"

#include "test/hftest.h"

/* Number of pages reserved for page tables. Increase if necessary. */
#define PTABLE_PAGES 3

alignas(alignof(struct mm_page_table)) static char ptable_buf
	[sizeof(struct mm_page_table) * PTABLE_PAGES];

static struct mpool ppool;
static struct mm_ptable ptable;

static struct mm_stage1_locked get_stage1_locked(void)
{
	return (struct mm_stage1_locked){.ptable = &ptable};
}

bool hftest_mm_init(void)
{
	struct mm_stage1_locked stage1_locked;

	mpool_init(&ppool, sizeof(struct mm_page_table));
	if (!mpool_add_chunk(&ppool, ptable_buf, sizeof(ptable_buf))) {
		HFTEST_FAIL(true, "Failed to add buffer to page-table pool.");
	}

	if (!mm_ptable_init(&ptable, MM_FLAG_STAGE1, &ppool)) {
		HFTEST_FAIL(true, "Unable to allocate memory for page table.");
	}

	stage1_locked = get_stage1_locked();
	mm_identity_map(stage1_locked, pa_init(0),
			pa_init(mm_ptable_addr_space_end(MM_FLAG_STAGE1)),
			MM_MODE_R | MM_MODE_W | MM_MODE_X, &ppool);

	if (!arch_vm_mm_init()) {
		return false;
	}

	arch_vm_mm_enable(ptable.root);

	return true;
}

void hftest_mm_identity_map(const void *base, size_t size, uint32_t mode)
{
	struct mm_stage1_locked stage1_locked = get_stage1_locked();
	paddr_t start = pa_from_va(va_from_ptr(base));
	paddr_t end = pa_add(start, size);

	if (mm_identity_map(stage1_locked, start, end, mode, &ppool) != base) {
		FAIL("Could not add new page table mapping. Try increasing "
		     "size of the page table buffer.");
	}
}

void hftest_mm_vcpu_init(void)
{
	arch_vm_mm_enable(ptable.root);
}
