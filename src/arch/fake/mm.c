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
 * The fake architecture uses the mode flags to represent the attributes applied
 * to memory. The flags are shifted to avoid equality of modes and attributes.
 */
#define PTE_ATTR_MODE_SHIFT 48
#define PTE_ATTR_MODE_MASK                                               \
	((uint64_t)(MM_MODE_R | MM_MODE_W | MM_MODE_X | MM_MODE_D |      \
		    MM_MODE_INVALID | MM_MODE_UNOWNED | MM_MODE_SHARED | \
		    MM_MODE_STAGE1)                                      \
	 << PTE_ATTR_MODE_SHIFT)

/* The bit to distinguish a table from a block is the highest of the page bits.
 */
#define PTE_TABLE (UINT64_C(1) << (PAGE_BITS - 1))

/* Mask for the address part of an entry. */
#define PTE_ADDR_MASK (~(PTE_ATTR_MODE_MASK | (UINT64_C(1) << PAGE_BITS) - 1))

/* Offset the bits of each level so they can't be misued. */
#define PTE_LEVEL_SHIFT(lvl) ((lvl)*2)

pte_t arch_mm_absent_pte(uint8_t level)
{
	return ((uint64_t)(MM_MODE_INVALID | MM_MODE_UNOWNED)
		<< PTE_ATTR_MODE_SHIFT) >>
	       PTE_LEVEL_SHIFT(level);
}

pte_t arch_mm_table_pte(uint8_t level, paddr_t pa)
{
	return (pa_addr(pa) | PTE_TABLE) >> PTE_LEVEL_SHIFT(level);
}

pte_t arch_mm_block_pte(uint8_t level, paddr_t pa, uint64_t attrs)
{
	return (pa_addr(pa) | attrs) >> PTE_LEVEL_SHIFT(level);
}

bool arch_mm_is_block_allowed(uint8_t level)
{
	(void)level;
	return true;
}

bool arch_mm_pte_is_present(pte_t pte, uint8_t level)
{
	return arch_mm_pte_is_valid(pte, level) ||
	       !(((pte << PTE_LEVEL_SHIFT(level)) >> PTE_ATTR_MODE_SHIFT) &
		 MM_MODE_UNOWNED);
}

bool arch_mm_pte_is_valid(pte_t pte, uint8_t level)
{
	return !(((pte << PTE_LEVEL_SHIFT(level)) >> PTE_ATTR_MODE_SHIFT) &
		 MM_MODE_INVALID);
}

bool arch_mm_pte_is_block(pte_t pte, uint8_t level)
{
	return arch_mm_pte_is_present(pte, level) &&
	       !arch_mm_pte_is_table(pte, level);
}

bool arch_mm_pte_is_table(pte_t pte, uint8_t level)
{
	return (pte << PTE_LEVEL_SHIFT(level)) & PTE_TABLE;
}

paddr_t arch_mm_clear_pa(paddr_t pa)
{
	return pa_init(pa_addr(pa) & PTE_ADDR_MASK);
}

paddr_t arch_mm_block_from_pte(pte_t pte, uint8_t level)
{
	return pa_init((pte << PTE_LEVEL_SHIFT(level)) & PTE_ADDR_MASK);
}

paddr_t arch_mm_table_from_pte(pte_t pte, uint8_t level)
{
	return pa_init((pte << PTE_LEVEL_SHIFT(level)) & PTE_ADDR_MASK);
}

uint64_t arch_mm_pte_attrs(pte_t pte, uint8_t level)
{
	return ((pte << PTE_LEVEL_SHIFT(level)) & PTE_ATTR_MODE_MASK) >>
	       PTE_ATTR_MODE_SHIFT;
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
	/* Stage-1 has no concatenated tables but stage 2 has 4 of them. */
	return (mode & MM_MODE_STAGE1) ? 1 : 4;
}

uint64_t arch_mm_mode_to_attrs(int mode)
{
	/* Stage-2 ignores the device mode. */
	if (!(mode & MM_MODE_STAGE1)) {
		mode &= ~MM_MODE_D;
	}

	return ((uint64_t)mode << PTE_ATTR_MODE_SHIFT) & PTE_ATTR_MODE_MASK;
}

bool arch_mm_init(paddr_t table, bool first)
{
	/* No initialization required. */
	(void)table;
	(void)first;
	return true;
}
