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

#pragma once

#include <stdbool.h>
#include <stddef.h>

#include "hf/addr.h"

/*
 * Our fake architecture has page tables rather similar to aarch64, but not
 * quite.
 * - The highest level table is always 2, lowest level is 0.
 * - Blocks are allowed at all levels.
 * There are four types of entries:
 * - Absent: 0
 * - Page, at level 0: <page-aligned address> | <attrs> | 0x3
 * - Block, at level 2 or 1: <block-aligned address> | <attrs> | 0x1
 * - Subtable, at level 2 or 1: <subtable address> | 0x3
 * <attrs> are always 0 for now.
 */

/* A page table entry. */
typedef uint64_t pte_t;

#define PAGE_LEVEL_BITS 9

/**
 * Returns the encoding of a page table entry that isn't present.
 */
static inline pte_t arch_mm_absent_pte(int level)
{
	return 0;
}

/**
 * Converts a physical address to a table PTE.
 *
 * The spec says that 'Table descriptors for stage 2 translations do not
 * include any attribute field', so we don't take any attributes as arguments.
 */
static inline pte_t arch_mm_table_pte(int level, paddr_t pa)
{
	/* This is the same for all levels on aarch64. */
	(void)level;
	return pa_addr(pa) | 0x3;
}

/**
 * Converts a physical address to a block PTE.
 *
 * The level must allow block entries.
 */
static inline pte_t arch_mm_block_pte(int level, paddr_t pa, uint64_t attrs)
{
	pte_t pte = pa_addr(pa) | attrs | 0x1;
	if (level == 0) {
		pte |= 0x2;
	}
	return pte;
}

/**
 * Specifies whether block mappings are acceptable at the given level.
 *
 * Level 0 must allow block entries.
 */
static inline bool arch_mm_is_block_allowed(int level)
{
	return level <= 2;
}

/**
 * Determines if the given pte is present, i.e., if it points to another table,
 * to a page, or a block of pages.
 */
static inline bool arch_mm_pte_is_present(pte_t pte, int level)
{
	return (pte & 0x1) != 0;
}

/**
 * Determines if the given pte references another table.
 */
static inline bool arch_mm_pte_is_table(pte_t pte, int level)
{
	return level != 0 && (pte & 0x3) == 0x3;
}

/**
 * Determines if the given pte references a block of pages.
 */
static inline bool arch_mm_pte_is_block(pte_t pte, int level)
{
	return arch_mm_is_block_allowed(level) &&
	       (pte & 0x3) == (level == 0 ? 0x3 : 0x1);
}

static inline uint64_t hf_arch_fake_mm_clear_pte_attrs(pte_t pte)
{
	return pte & ~0x3;
}

/**
 * Clears the given physical address, i.e., sets the ignored bits (from a page
 * table perspective) to zero.
 */
static inline paddr_t arch_mm_clear_pa(paddr_t pa)
{
	/* This is assumed to round down to the page boundary. */
	return pa_init(hf_arch_fake_mm_clear_pte_attrs(pa_addr(pa)) &
		       ~((1 << PAGE_BITS) - 1));
}

/**
 * Extracts the physical address of the block referred to by the given page
 * table entry.
 */
static inline paddr_t arch_mm_block_from_pte(pte_t pte)
{
	return pa_init(hf_arch_fake_mm_clear_pte_attrs(pte));
}

/**
 * Extracts the physical address of the page table referred to by the given page
 * table entry.
 */
static inline paddr_t arch_mm_table_from_pte(pte_t pte)
{
	return pa_init(hf_arch_fake_mm_clear_pte_attrs(pte));
}

/**
 * Extracts the architecture specific attributes applies to the given page table
 * entry.
 */
static inline uint64_t arch_mm_pte_attrs(pte_t pte)
{
	return 0;
}

/**
 * Given the attrs from a table at some level and the attrs from all the blocks
 * in that table, return equivalent attrs to use for a block which will replace
 * the entire table.
 */
static inline uint64_t arch_mm_combine_table_entry_attrs(uint64_t table_attrs,
							 uint64_t block_attrs)
{
	return table_attrs | block_attrs;
}

/**
 * Invalidates stage-1 TLB entries referring to the given virtual address range.
 */
static inline void arch_mm_invalidate_stage1_range(vaddr_t va_begin,
						   vaddr_t va_end)
{
}

/**
 * Invalidates stage-2 TLB entries referring to the given intermediate physical
 * address range.
 */
static inline void arch_mm_invalidate_stage2_range(ipaddr_t va_begin,
						   ipaddr_t va_end)
{
}

/**
 * Determines the maximum level supported by the given mode.
 */
static inline uint8_t arch_mm_max_level(int mode)
{
	(void)mode;
	return 2;
}

static inline uint64_t arch_mm_mode_to_attrs(int mode)
{
	(void)mode;
	return 0;
}

static inline bool arch_mm_init(paddr_t table, bool first)
{
	(void)table;
	(void)first;
	return true;
}
