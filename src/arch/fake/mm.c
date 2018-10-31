/*
 * Copyright 2018 Google LLC
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

#include "hf/arch/mm.h"

#include "hf/mm.h"

/*
 * Our fake architecture has page tables base on those of aarch64:
 *
 *  - The highest level table is always 2, lowest level is 0.
 *  - Blocks are allowed at all levels.
 *
 * There are four kinds of entry:
 *
 *  1. Absent: 0
 *  2. Page, at level 0: <page-aligned address> | <attrs> | 0x3
 *  3. Block, at level 2 or 1: <block-aligned address> | <attrs> | 0x1
 *  4. Subtable, at level 2 or 1: <subtable address> | 0x3
 *
 * <attrs> are always 0 for now.
 */

pte_t arch_mm_absent_pte(int level)
{
	(void)level;
	return 0;
}

pte_t arch_mm_table_pte(int level, paddr_t pa)
{
	/* This is the same for all levels. */
	(void)level;
	return pa_addr(pa) | 0x3;
}

pte_t arch_mm_block_pte(int level, paddr_t pa, uint64_t attrs)
{
	/* Single pages are encoded differently to larger blocks. */
	pte_t pte = pa_addr(pa) | attrs | 0x1;
	if (level == 0) {
		pte |= 0x2;
	}
	return pte;
}

bool arch_mm_is_block_allowed(int level)
{
	/* All levels can have blocks. */
	(void)level;
	return true;
}

bool arch_mm_pte_is_present(pte_t pte, int level)
{
	(void)level;
	return (pte & 0x1) != 0;
}

bool arch_mm_pte_is_table(pte_t pte, int level)
{
	/* Level 0 only contains pages so cannot be a table. */
	return level != 0 && (pte & 0x3) == 0x3;
}

bool arch_mm_pte_is_block(pte_t pte, int level)
{
	/* Single pages are encoded differently to larger blocks. */
	return arch_mm_is_block_allowed(level) &&
	       (pte & 0x3) == (level == 0 ? 0x3 : 0x1);
}

static uint64_t hf_arch_fake_mm_clear_pte_attrs(pte_t pte)
{
	return pte & ~0x3;
}

paddr_t arch_mm_clear_pa(paddr_t pa)
{
	/* This is assumed to round down to the page boundary. */
	return pa_init(hf_arch_fake_mm_clear_pte_attrs(pa_addr(pa)) &
		       ~((1 << PAGE_BITS) - 1));
}

paddr_t arch_mm_block_from_pte(pte_t pte)
{
	return pa_init(hf_arch_fake_mm_clear_pte_attrs(pte));
}

paddr_t arch_mm_table_from_pte(pte_t pte)
{
	return pa_init(hf_arch_fake_mm_clear_pte_attrs(pte));
}

uint64_t arch_mm_pte_attrs(pte_t pte)
{
	/* Attributes are not modelled. */
	(void)pte;
	return 0;
}

uint64_t arch_mm_combine_table_entry_attrs(uint64_t table_attrs,
					   uint64_t block_attrs)
{
	return table_attrs | block_attrs;
}

void arch_mm_invalidate_stage1_range(vaddr_t va_begin, vaddr_t va_end)
{
	/* There's no modelling of the stage-1 TLB. */
}

void arch_mm_invalidate_stage2_range(ipaddr_t va_begin, ipaddr_t va_end)
{
	/* There's no modelling of the stage-2 TLB. */
}

uint8_t arch_mm_max_level(int mode)
{
	/* All modes have 3 levels in the page table. */
	(void)mode;
	return 2;
}

uint8_t arch_mm_root_table_count(int mode)
{
	/* Stage 1 has no concatenated tables but stage 2 has 4 of them. */
	return (mode & MM_MODE_STAGE1) ? 1 : 4;
}

uint64_t arch_mm_mode_to_attrs(int mode)
{
	/* Attributes are not modelled. */
	(void)mode;
	return 0;
}

bool arch_mm_init(paddr_t table, bool first)
{
	/* No initialization required. */
	(void)table;
	(void)first;
	return true;
}
