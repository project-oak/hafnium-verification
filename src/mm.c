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

#include "hf/mm.h"

#include <assert.h>
#include <stdatomic.h>
#include <stdint.h>

#include "hf/alloc.h"
#include "hf/dlog.h"
#include "hf/layout.h"

/**
 * This file has functions for managing the level 1 and 2 page tables used by
 * Hafnium. There is a level 1 mapping used by Hafnium itself to access memory,
 * and then a level 2 mapping per VM. The design assumes that all page tables
 * contain only 1-1 mappings, aligned on the block boundaries.
 */

/* The type of addresses stored in the page table. */
typedef uintvaddr_t ptable_addr_t;

/*
 * For stage 2, the input is an intermediate physical addresses rather than a
 * virtual address so:
 */
static_assert(
	sizeof(ptable_addr_t) == sizeof(uintpaddr_t),
	"Currently, the same code manages the stage 1 and stage 2 page tables "
	"which only works if the virtual and intermediate physical addresses "
	"are the same size. It looks like that assumption might not be holding "
	"so we need to check that everything is going to be ok.");

/* Keep macro alignment */
/* clang-format off */

#define MAP_FLAG_NOSYNC 0x01
#define MAP_FLAG_COMMIT 0x02
#define MAP_FLAG_UNMAP  0x04

/* clang-format on */

static struct mm_ptable ptable;

/**
 * Get the page table from the physical address.
 */
static struct mm_page_table *mm_page_table_from_pa(paddr_t pa)
{
	return ptr_from_va(va_from_pa(pa));
}

/**
 * Rounds an address down to a page boundary.
 */
static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr)
{
	return addr & ~((ptable_addr_t)(PAGE_SIZE - 1));
}

/**
 * Rounds an address up to a page boundary.
 */
static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr)
{
	return mm_round_down_to_page(addr + PAGE_SIZE - 1);
}

/**
 * Calculates the size of the address space represented by a page table entry at
 * the given level.
 */
static size_t mm_entry_size(uint8_t level)
{
	return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
}

/**
 * For a given address, calculates the maximum (plus one) address that can be
 * represented by the same table at the given level.
 */
static ptable_addr_t mm_level_end(ptable_addr_t addr, uint8_t level)
{
	size_t offset = PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS;
	return ((addr >> offset) + 1) << offset;
}

/**
 * For a given address, calculates the index at which its entry is stored in a
 * table at the given level.
 */
static size_t mm_index(ptable_addr_t addr, uint8_t level)
{
	ptable_addr_t v = addr >> (PAGE_BITS + level * PAGE_LEVEL_BITS);
	return v & ((UINT64_C(1) << PAGE_LEVEL_BITS) - 1);
}

/**
 * Allocate a new page table.
 */
static struct mm_page_table *mm_alloc_page_table(bool nosync)
{
	if (nosync) {
		return halloc_aligned_nosync(sizeof(struct mm_page_table),
					     alignof(struct mm_page_table));
	}

	return halloc_aligned(sizeof(struct mm_page_table),
			      alignof(struct mm_page_table));
}

/**
 * Populates the provided page table entry with a reference to another table if
 * needed, that is, if it does not yet point to another table.
 *
 * Returns a pointer to the table the entry now points to.
 */
static struct mm_page_table *mm_populate_table_pte(pte_t *pte, uint8_t level,
						   bool nosync)
{
	struct mm_page_table *ntable;
	pte_t v = *pte;
	pte_t new_pte;
	size_t i;
	size_t inc;
	uint8_t level_below = level - 1;

	/* Just return pointer to table if it's already populated. */
	if (arch_mm_pte_is_table(v, level)) {
		return mm_page_table_from_pa(arch_mm_table_from_pte(v));
	}

	/* Allocate a new table. */
	ntable = mm_alloc_page_table(nosync);
	if (ntable == NULL) {
		dlog("Failed to allocate memory for page table\n");
		return NULL;
	}

	/* Determine template for new pte and its increment. */
	if (arch_mm_pte_is_block(v, level)) {
		inc = mm_entry_size(level_below);
		new_pte = arch_mm_block_pte(level_below,
					    arch_mm_block_from_pte(v),
					    arch_mm_pte_attrs(v));
	} else {
		inc = 0;
		new_pte = arch_mm_absent_pte(level_below);
	}

	/* Initialise entries in the new table. */
	for (i = 0; i < MM_PTE_PER_PAGE; i++) {
		ntable->entries[i] = new_pte;
		new_pte += inc;
	}

	/*
	 * Ensure initialisation is visible before updating the actual pte, then
	 * update it.
	 */
	atomic_thread_fence(memory_order_release);
	*pte = arch_mm_table_pte(level, pa_init((uintpaddr_t)ntable));

	return ntable;
}

/**
 * Frees all page-table-related memory associated with the given pte at the
 * given level, including any subtables recursively.
 */
static void mm_free_page_pte(pte_t pte, uint8_t level)
{
	struct mm_page_table *table;
	uint64_t i;

	if (!arch_mm_pte_is_table(pte, level)) {
		return;
	}

	table = mm_page_table_from_pa(arch_mm_table_from_pte(pte));
	/* Recursively free any subtables. */
	for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
		mm_free_page_pte(table->entries[i], level - 1);
	}

	/* Free the table itself. */
	hfree(table);
}

/**
 * Returns whether all entries in this table are absent.
 */
static bool mm_ptable_is_empty(struct mm_page_table *table, uint8_t level)
{
	uint64_t i;

	for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
		if (arch_mm_pte_is_present(table->entries[i], level)) {
			return false;
		}
	}
	return true;
}

/**
 * Updates the page table at the given level to map the given address range to a
 * physical range using the provided (architecture-specific) attributes. Or if
 * MAP_FLAG_UNMAP is set, unmap the given range instead.
 *
 * This function calls itself recursively if it needs to update additional
 * levels, but the recursion is bound by the maximum number of levels in a page
 * table.
 */
static bool mm_map_level(ptable_addr_t begin, ptable_addr_t end, paddr_t pa,
			 uint64_t attrs, struct mm_page_table *table,
			 uint8_t level, int flags)
{
	pte_t *pte = &table->entries[mm_index(begin, level)];
	ptable_addr_t level_end = mm_level_end(begin, level);
	size_t entry_size = mm_entry_size(level);
	bool commit = flags & MAP_FLAG_COMMIT;
	bool nosync = flags & MAP_FLAG_NOSYNC;
	bool unmap = flags & MAP_FLAG_UNMAP;

	/* Cap end so that we don't go over the current level max. */
	if (end > level_end) {
		end = level_end;
	}

	/* Fill each entry in the table. */
	while (begin < end) {
		if (unmap ? !arch_mm_pte_is_present(*pte, level)
			  : arch_mm_pte_is_block(*pte, level) &&
				    arch_mm_pte_attrs(*pte) == attrs) {
			/*
			 * If the entry is already mapped with the right
			 * attributes, or already absent in the case of
			 * unmapping, no need to do anything; carry on to the
			 * next entry.
			 */
		} else if ((end - begin) >= entry_size &&
			   (unmap || arch_mm_is_block_allowed(level)) &&
			   (begin & (entry_size - 1)) == 0) {
			/*
			 * If the entire entry is within the region we want to
			 * map, map/unmap the whole entry.
			 */
			if (commit) {
				pte_t v = *pte;
				*pte = unmap ? arch_mm_absent_pte(level)
					     : arch_mm_block_pte(level, pa,
								 attrs);
				/* TODO: Add barrier. How do we ensure this
				 * isn't in use by another CPU? Send IPI? */
				mm_free_page_pte(v, level);
			}
		} else {
			/*
			 * If the entry is already a subtable get it; otherwise
			 * replace it with an equivalent subtable and get that.
			 */
			struct mm_page_table *nt =
				mm_populate_table_pte(pte, level, nosync);
			if (nt == NULL) {
				return false;
			}

			/*
			 * Recurse to map/unmap the appropriate entries within
			 * the subtable.
			 */
			if (!mm_map_level(begin, end, pa, attrs, nt, level - 1,
					  flags)) {
				return false;
			}

			/*
			 * If the subtable is now empty, replace it with an
			 * absent entry at this level.
			 */
			if (commit && unmap &&
			    mm_ptable_is_empty(nt, level - 1)) {
				pte_t v = *pte;
				*pte = arch_mm_absent_pte(level);
				/* TODO: Add barrier. How do we ensure this
				 * isn't in use by another CPU? Send IPI? */
				mm_free_page_pte(v, level);
			}
		}

		begin = (begin + entry_size) & ~(entry_size - 1);
		pa = pa_init((pa_addr(pa) + entry_size) & ~(entry_size - 1));
		pte++;
	}

	return true;
}

/**
 * Invalidates the TLB for the given address range.
 */
static void mm_invalidate_tlb(ptable_addr_t begin, ptable_addr_t end,
			      bool stage1)
{
	if (stage1) {
		arch_mm_invalidate_stage1_range(va_init(begin), va_init(end));
	} else {
		arch_mm_invalidate_stage2_range(ipa_init(begin), ipa_init(end));
	}
}

/**
 * Updates the given table such that the given physical address range is mapped
 * or not mapped into the address space with the architecture-agnostic mode
 * provided.
 */
static bool mm_ptable_identity_update(struct mm_ptable *t, paddr_t pa_begin,
				      paddr_t pa_end, int mode, bool unmap)
{
	uint64_t attrs = unmap ? 0 : arch_mm_mode_to_attrs(mode);
	int flags = (mode & MM_MODE_NOSYNC ? MAP_FLAG_NOSYNC : 0) |
		    (unmap ? MAP_FLAG_UNMAP : 0);
	uint8_t level = arch_mm_max_level(mode);
	struct mm_page_table *table = mm_page_table_from_pa(t->table);
	ptable_addr_t begin;
	ptable_addr_t end;

	pa_begin = arch_mm_clear_pa(pa_begin);
	begin = pa_addr(pa_begin);
	end = mm_round_up_to_page(pa_addr(pa_end));

	/*
	 * Do it in two steps to prevent leaving the table in a halfway updated
	 * state. In such a two-step implementation, the table may be left with
	 * extra internal tables, but no different mapping on failure.
	 */
	if (!mm_map_level(begin, end, pa_begin, attrs, table, level, flags)) {
		return false;
	}

	mm_map_level(begin, end, pa_begin, attrs, table, level,
		     flags | MAP_FLAG_COMMIT);

	/* Invalidate the tlb. */
	if (!(mode & MM_MODE_NOINVALIDATE)) {
		mm_invalidate_tlb(begin, end, (mode & MM_MODE_STAGE1) != 0);
	}

	return true;
}

/**
 * Updates the given table such that the given physical address range is mapped
 * into the address space with the architecture-agnostic mode provided.
 */
static bool mm_ptable_identity_map(struct mm_ptable *t, paddr_t pa_begin,
				   paddr_t pa_end, int mode)
{
	return mm_ptable_identity_update(t, pa_begin, pa_end, mode, false);
}

/**
 * Updates the given table such that the given physical address range is not
 * mapped into the address space.
 */
static bool mm_ptable_unmap(struct mm_ptable *t, paddr_t pa_begin,
			    paddr_t pa_end, int mode)
{
	return mm_ptable_identity_update(t, pa_begin, pa_end, mode, true);
}

/**
 * Writes the given table to the debug log, calling itself recursively to
 * write sub-tables.
 */
static void mm_dump_table_recursive(struct mm_page_table *table, uint8_t level,
				    int max_level)
{
	uint64_t i;
	for (i = 0; i < MM_PTE_PER_PAGE; i++) {
		if (!arch_mm_pte_is_present(table->entries[i], level)) {
			continue;
		}

		dlog("%*s%x: %x\n", 4 * (max_level - level), "", i,
		     table->entries[i]);

		if (arch_mm_pte_is_table(table->entries[i], level)) {
			mm_dump_table_recursive(
				mm_page_table_from_pa(arch_mm_table_from_pte(
					table->entries[i])),
				level - 1, max_level);
		}
	}
}

/**
 * Write the given table to the debug log.
 */
void mm_ptable_dump(struct mm_ptable *t, int mode)
{
	struct mm_page_table *table = mm_page_table_from_pa(t->table);
	int max_level = arch_mm_max_level(mode);
	mm_dump_table_recursive(table, max_level, max_level);
}

/**
 * Given that `entry` is a subtable but its entries are all absent, return the
 * absent entry with which it can be replaced. Note that `entry` will no longer
 * be valid after calling this function as the subtable will have been freed.
 */
static pte_t mm_table_pte_to_absent(pte_t entry, uint8_t level)
{
	struct mm_page_table *table =
		mm_page_table_from_pa(arch_mm_table_from_pte(entry));
	/*
	 * Free the subtable. This is safe to do directly (rather than
	 * using mm_free_page_pte) because we know by this point that it
	 * doesn't have any subtables of its own.
	 */
	hfree(table);
	/* Replace subtable with a single absent entry. */
	return arch_mm_absent_pte(level);
}

/**
 * Given that `entry` is a subtable and its entries are all identical, return
 * the single block entry with which it can be replaced if possible. Note that
 * `entry` will no longer be valid after calling this function as the subtable
 * may have been freed.
 */
static pte_t mm_table_pte_to_block(pte_t entry, uint8_t level)
{
	struct mm_page_table *table;
	uint64_t block_attrs;
	uint64_t table_attrs;
	uint64_t combined_attrs;
	paddr_t block_address;

	if (!arch_mm_is_block_allowed(level)) {
		return entry;
	}

	table = mm_page_table_from_pa(arch_mm_table_from_pte(entry));
	/*
	 * Replace subtable with a single block, with equivalent
	 * attributes.
	 */
	block_attrs = arch_mm_pte_attrs(table->entries[0]);
	table_attrs = arch_mm_pte_attrs(entry);
	combined_attrs =
		arch_mm_combine_table_entry_attrs(table_attrs, block_attrs);
	block_address = arch_mm_block_from_pte(table->entries[0]);
	/* Free the subtable. */
	hfree(table);
	/*
	 * We can assume that the block is aligned properly
	 * because all virtual addresses are aligned by
	 * definition, and we have a 1-1 mapping from virtual to
	 * physical addresses.
	 */
	return arch_mm_block_pte(level, block_address, combined_attrs);
}

/**
 * Defragment the given ptable entry by recursively replacing any tables with
 * block or absent entries where possible.
 */
static pte_t mm_ptable_defrag_entry(pte_t entry, uint8_t level)
{
	struct mm_page_table *table;
	uint64_t i;
	uint64_t attrs;
	bool identical_blocks_so_far = true;
	bool all_absent_so_far = true;

	if (!arch_mm_pte_is_table(entry, level)) {
		return entry;
	}

	table = mm_page_table_from_pa(arch_mm_table_from_pte(entry));

	/*
	 * Check if all entries are blocks with the same flags or are all
	 * absent.
	 */
	attrs = arch_mm_pte_attrs(table->entries[0]);
	for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
		/*
		 * First try to defrag the entry, in case it is a subtable.
		 */
		table->entries[i] =
			mm_ptable_defrag_entry(table->entries[i], level - 1);

		if (arch_mm_pte_is_present(table->entries[i], level - 1)) {
			all_absent_so_far = false;
		}

		/*
		 * If the entry is a block, check that the flags are the same as
		 * what we have so far.
		 */
		if (!arch_mm_pte_is_block(table->entries[i], level - 1) ||
		    arch_mm_pte_attrs(table->entries[i]) != attrs) {
			identical_blocks_so_far = false;
		}
	}
	if (identical_blocks_so_far) {
		return mm_table_pte_to_block(entry, level);
	}
	if (all_absent_so_far) {
		return mm_table_pte_to_absent(entry, level);
	}
	return entry;
}

/**
 * Defragments the given page table by converting page table references to
 * blocks whenever possible.
 */
void mm_ptable_defrag(struct mm_ptable *t, int mode)
{
	struct mm_page_table *table = mm_page_table_from_pa(t->table);
	uint8_t level = arch_mm_max_level(mode);
	uint64_t i;

	/*
	 * Loop through each entry in the table. If it points to another table,
	 * check if that table can be replaced by a block or an absent entry.
	 */
	for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
		table->entries[i] =
			mm_ptable_defrag_entry(table->entries[i], level);
	}
}

/**
 * Unmaps the hypervisor pages from the given page table.
 */
bool mm_ptable_unmap_hypervisor(struct mm_ptable *t, int mode)
{
	/* TODO: If we add pages dynamically, they must be included here too. */
	return mm_ptable_unmap(t, layout_text_begin(), layout_text_end(),
			       mode) &&
	       mm_ptable_unmap(t, layout_rodata_begin(), layout_rodata_end(),
			       mode) &&
	       mm_ptable_unmap(t, layout_data_begin(), layout_data_end(), mode);
}

/**
 * Determines if the given address is mapped in the given page table by
 * recursively traversing all levels of the page table.
 */
static bool mm_is_mapped_recursive(struct mm_page_table *table,
				   ptable_addr_t addr, uint8_t level)
{
	pte_t pte;
	ptable_addr_t va_level_end = mm_level_end(addr, level);

	/* It isn't mapped if it doesn't fit in the table. */
	if (addr >= va_level_end) {
		return false;
	}

	pte = table->entries[mm_index(addr, level)];

	if (arch_mm_pte_is_block(pte, level)) {
		return true;
	}

	if (arch_mm_pte_is_table(pte, level)) {
		return mm_is_mapped_recursive(
			mm_page_table_from_pa(arch_mm_table_from_pte(pte)),
			addr, level - 1);
	}

	/* The entry is not present. */
	return false;
}

/**
 * Determines if the given address is mapped in the given page table.
 */
static bool mm_ptable_is_mapped(struct mm_ptable *t, ptable_addr_t addr,
				int mode)
{
	struct mm_page_table *table = mm_page_table_from_pa(t->table);
	uint8_t level = arch_mm_max_level(mode);

	addr = mm_round_down_to_page(addr);

	return mm_is_mapped_recursive(table, addr, level);
}

/**
 * Initialises the given page table.
 */
bool mm_ptable_init(struct mm_ptable *t, int mode)
{
	size_t i;
	struct mm_page_table *table;

	table = mm_alloc_page_table(mode & MM_MODE_NOSYNC);
	if (table == NULL) {
		return false;
	}

	for (i = 0; i < MM_PTE_PER_PAGE; i++) {
		table->entries[i] = arch_mm_absent_pte(arch_mm_max_level(mode));
	}

	/* TODO: halloc could return a virtual or physical address if mm not
	 * enabled? */
	t->table = pa_init((uintpaddr_t)table);

	return true;
}

/**
 * Updates a VM's page table such that the given physical address range is
 * mapped in the address space at the corresponding address range in the
 * architecture-agnostic mode provided.
 */
bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
			int mode, ipaddr_t *ipa)
{
	bool success =
		mm_ptable_identity_map(t, begin, end, mode & ~MM_MODE_STAGE1);

	if (success && ipa != NULL) {
		*ipa = ipa_from_pa(begin);
	}

	return success;
}

/**
 * Updates the VM's table such that the given physical address range is not
 * mapped in the address space.
 */
bool mm_vm_unmap(struct mm_ptable *t, paddr_t begin, paddr_t end, int mode)
{
	return mm_ptable_unmap(t, begin, end, mode & ~MM_MODE_STAGE1);
}

/**
 * Checks whether the given intermediate physical addess is mapped in the given
 * page table of a VM.
 */
bool mm_vm_is_mapped(struct mm_ptable *t, ipaddr_t ipa, int mode)
{
	return mm_ptable_is_mapped(t, ipa_addr(ipa), mode & ~MM_MODE_STAGE1);
}

/**
 * Translates an intermediate physical address to a physical address. Addresses
 * are currently identity mapped so this is a simple type convertion. Returns
 * true if the address was mapped in the table and the address was converted.
 */
bool mm_vm_translate(struct mm_ptable *t, ipaddr_t ipa, paddr_t *pa)
{
	bool mapped = mm_vm_is_mapped(t, ipa, 0);

	if (mapped) {
		*pa = pa_init(ipa_addr(ipa));
	}

	return mapped;
}

/**
 * Updates the hypervisor page table such that the given physical address range
 * is mapped into the address space at the corresponding address range in the
 * architecture-agnostic mode provided.
 */
void *mm_identity_map(paddr_t begin, paddr_t end, int mode)
{
	if (mm_ptable_identity_map(&ptable, begin, end,
				   mode | MM_MODE_STAGE1)) {
		return ptr_from_va(va_from_pa(begin));
	}

	return NULL;
}

/**
 * Updates the hypervisor table such that the given physical address range is
 * not mapped in the address space.
 */
bool mm_unmap(paddr_t begin, paddr_t end, int mode)
{
	return mm_ptable_unmap(&ptable, begin, end, mode | MM_MODE_STAGE1);
}

/**
 * Initialises memory management for the hypervisor itself.
 */
bool mm_init(void)
{
	dlog_nosync("text: 0x%x - 0x%x\n", pa_addr(layout_text_begin()),
		    pa_addr(layout_text_end()));
	dlog_nosync("rodata: 0x%x - 0x%x\n", pa_addr(layout_rodata_begin()),
		    pa_addr(layout_rodata_end()));
	dlog_nosync("data: 0x%x - 0x%x\n", pa_addr(layout_data_begin()),
		    pa_addr(layout_data_end()));

	if (!mm_ptable_init(&ptable, MM_MODE_NOSYNC | MM_MODE_STAGE1)) {
		dlog_nosync("Unable to allocate memory for page table.\n");
		return false;
	}

	/* Map page for uart. */
	/* TODO: We may not want to map this. */
	mm_ptable_identity_map(&ptable, pa_init(PL011_BASE),
			       pa_add(pa_init(PL011_BASE), PAGE_SIZE),
			       MM_MODE_R | MM_MODE_W | MM_MODE_D |
				       MM_MODE_NOSYNC | MM_MODE_STAGE1);

	/* Map each section. */
	mm_identity_map(layout_text_begin(), layout_text_end(),
			MM_MODE_X | MM_MODE_NOSYNC);

	mm_identity_map(layout_rodata_begin(), layout_rodata_end(),
			MM_MODE_R | MM_MODE_NOSYNC);

	mm_identity_map(layout_data_begin(), layout_data_end(),
			MM_MODE_R | MM_MODE_W | MM_MODE_NOSYNC);

	return arch_mm_init(ptable.table, true);
}

bool mm_cpu_init(void)
{
	return arch_mm_init(ptable.table, false);
}

/**
 * Defragments the hypervisor page table.
 */
void mm_defrag(void)
{
	mm_ptable_defrag(&ptable, MM_MODE_STAGE1);
}
