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
 * A page table entry (PTE) will take one of the following forms:
 *
 *  1. absent        : There is no mapping.
 *  2. invalid block : Represents a block that is not in the address space.
 *  3. valid block   : Represents a block that is in the address space.
 *  4. table         : Represents a reference to a table of PTEs.
 */

/**
 * Creates an absent PTE.
 */
pte_t arch_mm_absent_pte(uint8_t level);

/**
 * Creates a table PTE.
 */
pte_t arch_mm_table_pte(uint8_t level, paddr_t pa);

/**
 * Creates a block PTE.
 */
pte_t arch_mm_block_pte(uint8_t level, paddr_t pa, uint64_t attrs);

/**
 * Checks whether a block is allowed at the given level of the page table.
 */
bool arch_mm_is_block_allowed(uint8_t level);

/**
 * Determines if a PTE is present i.e. it contains information and therefore
 * needs to exist in the page table. Any non-absent PTE is present.
 */
bool arch_mm_pte_is_present(pte_t pte, uint8_t level);

/**
 * Determines if a PTE is valid i.e. it can affect the address space. Tables and
 * valid blocks fall into this category. Invalid blocks do not as they hold
 * information about blocks that are not in the address space.
 */
bool arch_mm_pte_is_valid(pte_t pte, uint8_t level);

/**
 * Determines if a PTE is a block and represents an address range, valid or
 * invalid.
 */
bool arch_mm_pte_is_block(pte_t pte, uint8_t level);

/**
 * Determines if a PTE represents a reference to a table of PTEs.
 */
bool arch_mm_pte_is_table(pte_t pte, uint8_t level);

/**
 * Clears the bits of an address that are ignored by the page table. In effect,
 * the address is rounded down to the start of the corresponding PTE range.
 */
paddr_t arch_mm_clear_pa(paddr_t pa);

/**
 * Extracts the start address of the PTE range.
 */
paddr_t arch_mm_block_from_pte(pte_t pte, uint8_t level);

/**
 * Extracts the address of the table referenced by the PTE.
 */
paddr_t arch_mm_table_from_pte(pte_t pte, uint8_t level);

/**
 * Extracts the attributes of the PTE.
 */
uint64_t arch_mm_pte_attrs(pte_t pte, uint8_t level);

/**
 * Merges the attributes of a block into those of its containing table.
 */
uint64_t arch_mm_combine_table_entry_attrs(uint64_t table_attrs,
					   uint64_t block_attrs);

/**
 * Invalidates the given range of stage-1 TLB.
 */
void arch_mm_invalidate_stage1_range(vaddr_t va_begin, vaddr_t va_end);

/**
 * Invalidates the given range of stage-2 TLB.
 */
void arch_mm_invalidate_stage2_range(ipaddr_t va_begin, ipaddr_t va_end);

/**
 * Writes the given range of virtual memory back to the point of unification so
 * all cores and devices will see the updated values.
 */
void arch_mm_write_back_dcache(void *base, size_t size);

/**
 * Gets the maximum level allowed in the page table for stage-1.
 */
uint8_t arch_mm_stage1_max_level(void);

/**
 * Gets the maximum level allowed in the page table for stage-2.
 */
uint8_t arch_mm_stage2_max_level(void);

/**
 * Gets the number of concatenated page tables used at the root for stage-1.
 *
 * Tables are concatenated at the root to avoid introducing another level in the
 * page table meaning the table is shallow and wide. Each level is an extra
 * memory access when walking the table so keeping it shallow reduces the memory
 * accesses to aid performance.
 */
uint8_t arch_mm_stage1_root_table_count(void);

/**
 * Gets the number of concatenated page tables used at the root for stage-2.
 */
uint8_t arch_mm_stage2_root_table_count(void);

/**
 * Converts the mode into stage-1 attributes for a block PTE.
 */
uint64_t arch_mm_mode_to_stage1_attrs(int mode);

/**
 * Converts the mode into stage-2 attributes for a block PTE.
 */
uint64_t arch_mm_mode_to_stage2_attrs(int mode);

/**
 * Converts the stage-2 block attributes back to the corresponding mode.
 */
int arch_mm_stage2_attrs_to_mode(uint64_t attrs);

/**
 * Initializes the arch specific memory management state.
 */
bool arch_mm_init(paddr_t table, bool first);
