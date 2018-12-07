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

#include "hf/addr.h"

/** A page table entry. */
typedef uint64_t pte_t;

#define PAGE_LEVEL_BITS 9

/*
 * TODO: move the arch_mm_* declarations to a shared header. That header can
 * also check that the specific implementation defines everything it needs to
 * too.
 */
pte_t arch_mm_absent_pte(int level);
pte_t arch_mm_table_pte(int level, paddr_t pa);
pte_t arch_mm_block_pte(int level, paddr_t pa, uint64_t attrs);
bool arch_mm_is_block_allowed(int level);
bool arch_mm_pte_is_present(pte_t pte, int level);
bool arch_mm_pte_is_valid(pte_t pte, int level);
bool arch_mm_pte_is_table(pte_t pte, int level);
bool arch_mm_pte_is_block(pte_t pte, int level);
paddr_t arch_mm_clear_pa(paddr_t pa);
paddr_t arch_mm_block_from_pte(pte_t pte);
paddr_t arch_mm_table_from_pte(pte_t pte);
uint64_t arch_mm_pte_attrs(pte_t pte);
uint64_t arch_mm_combine_table_entry_attrs(uint64_t table_attrs,
					   uint64_t block_attrs);
void arch_mm_invalidate_stage1_range(vaddr_t va_begin, vaddr_t va_end);
void arch_mm_invalidate_stage2_range(ipaddr_t va_begin, ipaddr_t va_end);
uint8_t arch_mm_max_level(int mode);
uint8_t arch_mm_root_table_count(int mode);
uint64_t arch_mm_mode_to_attrs(int mode);
bool arch_mm_init(paddr_t table, bool first);
