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

#define MAP_FLAG_COMMIT 0x01
#define MAP_FLAG_UNMAP  0x02
#define MAP_FLAG_NOBBM  0x04
#define MAP_FLAG_STAGE1 0x08

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
 * Gets the address of the start of the next block of the given size. The size
 * must be a power of two.
 */
static ptable_addr_t mm_start_of_next_block(ptable_addr_t addr,
					    size_t block_size)
{
	return (addr + block_size) & ~(block_size - 1);
}

/**
 * Gets the physical address of the start of the next block of the given size.
 * The size must be a power of two.
 */
static paddr_t mm_pa_start_of_next_block(paddr_t pa, size_t block_size)
{
	return pa_init((pa_addr(pa) + block_size) & ~(block_size - 1));
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
 * Allocates a new page table.
 */
static struct mm_page_table *mm_alloc_page_tables(size_t count,
						  struct mpool *ppool)
{
	if (count == 1) {
		return mpool_alloc(ppool);
	}

	return mpool_alloc_contiguous(ppool, count, count);
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
 * Frees all page-table-related memory associated with the given pte at the
 * given level, including any subtables recursively.
 */
static void mm_free_page_pte(pte_t pte, uint8_t level, struct mpool *ppool)
{
	struct mm_page_table *table;
	uint64_t i;

	if (!arch_mm_pte_is_table(pte, level)) {
		return;
	}

	/* Recursively free any subtables. */
	table = mm_page_table_from_pa(arch_mm_table_from_pte(pte, level));
	for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
		mm_free_page_pte(table->entries[i], level - 1, ppool);
	}

	/* Free the table itself. */
	mpool_free(ppool, table);
}

/**
 * Replaces a page table entry with the given value. If both old and new values
 * are valid, it performs a break-before-make sequence where it first writes an
 * invalid value to the PTE, flushes the TLB, then writes the actual new value.
 * This is to prevent cases where CPUs have different 'valid' values in their
 * TLBs, which may result in issues for example in cache coherency.
 */
static void mm_replace_entry(ptable_addr_t begin, pte_t *pte, pte_t new_pte,
			     uint8_t level, int flags, struct mpool *ppool)
{
	pte_t v = *pte;

	/*
	 * We need to do the break-before-make sequence if both values are
	 * present, and if it hasn't been inhibited by the NOBBM flag.
	 */
	if (!(flags & MAP_FLAG_NOBBM) && arch_mm_pte_is_valid(v, level) &&
	    arch_mm_pte_is_valid(new_pte, level)) {
		*pte = arch_mm_absent_pte(level);
		mm_invalidate_tlb(begin, begin + mm_entry_size(level),
				  flags & MAP_FLAG_STAGE1);
	}

	/* Assign the new pte. */
	*pte = new_pte;

	/* Free pages that aren't in use anymore. */
	mm_free_page_pte(v, level, ppool);
}

/**
 * Populates the provided page table entry with a reference to another table if
 * needed, that is, if it does not yet point to another table.
 *
 * Returns a pointer to the table the entry now points to.
 */
static struct mm_page_table *mm_populate_table_pte(ptable_addr_t begin,
						   pte_t *pte, uint8_t level,
						   int flags,
						   struct mpool *ppool)
{
	struct mm_page_table *ntable;
	pte_t v = *pte;
	pte_t new_pte;
	size_t i;
	size_t inc;
	uint8_t level_below = level - 1;

	/* Just return pointer to table if it's already populated. */
	if (arch_mm_pte_is_table(v, level)) {
		return mm_page_table_from_pa(arch_mm_table_from_pte(v, level));
	}

	/* Allocate a new table. */
	ntable = mm_alloc_page_tables(1, ppool);
	if (ntable == NULL) {
		dlog("Failed to allocate memory for page table\n");
		return NULL;
	}

	/* Determine template for new pte and its increment. */
	if (arch_mm_pte_is_block(v, level)) {
		inc = mm_entry_size(level_below);
		new_pte = arch_mm_block_pte(level_below,
					    arch_mm_block_from_pte(v, level),
					    arch_mm_pte_attrs(v, level));
	} else {
		inc = 0;
		new_pte = arch_mm_absent_pte(level_below);
	}

	/* Initialise entries in the new table. */
	for (i = 0; i < MM_PTE_PER_PAGE; i++) {
		ntable->entries[i] = new_pte;
		new_pte += inc;
	}

	/* Ensure initialisation is visible before updating the pte. */
	atomic_thread_fence(memory_order_release);

	/* Replace the pte entry, doing a break-before-make if needed. */
	mm_replace_entry(begin, pte,
			 arch_mm_table_pte(level, pa_init((uintpaddr_t)ntable)),
			 level, flags, ppool);

	return ntable;
}

/**
 * Returns whether all entries in this table are absent.
 */
static bool mm_page_table_is_empty(struct mm_page_table *table, uint8_t level)
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
			 uint8_t level, int flags, struct mpool *ppool)
{
	pte_t *pte = &table->entries[mm_index(begin, level)];
	ptable_addr_t level_end = mm_level_end(begin, level);
	size_t entry_size = mm_entry_size(level);
	bool commit = flags & MAP_FLAG_COMMIT;
	bool unmap = flags & MAP_FLAG_UNMAP;

	/* Cap end so that we don't go over the current level max. */
	if (end > level_end) {
		end = level_end;
	}

	/* Fill each entry in the table. */
	while (begin < end) {
		if (unmap ? !arch_mm_pte_is_present(*pte, level)
			  : arch_mm_pte_is_block(*pte, level) &&
				    arch_mm_pte_attrs(*pte, level) == attrs) {
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
				pte_t new_pte =
					unmap ? arch_mm_absent_pte(level)
					      : arch_mm_block_pte(level, pa,
								  attrs);
				mm_replace_entry(begin, pte, new_pte, level,
						 flags, ppool);
			}
		} else {
			/*
			 * If the entry is already a subtable get it; otherwise
			 * replace it with an equivalent subtable and get that.
			 */
			struct mm_page_table *nt = mm_populate_table_pte(
				begin, pte, level, flags, ppool);
			if (nt == NULL) {
				return false;
			}

			/*
			 * Recurse to map/unmap the appropriate entries within
			 * the subtable.
			 */
			if (!mm_map_level(begin, end, pa, attrs, nt, level - 1,
					  flags, ppool)) {
				return false;
			}

			/*
			 * If the subtable is now empty, replace it with an
			 * absent entry at this level. We never need to do
			 * break-before-makes here because we are assigning
			 * an absent value.
			 */
			if (commit && unmap &&
			    mm_page_table_is_empty(nt, level - 1)) {
				pte_t v = *pte;
				*pte = arch_mm_absent_pte(level);
				mm_free_page_pte(v, level, ppool);
			}
		}

		begin = mm_start_of_next_block(begin, entry_size);
		pa = mm_pa_start_of_next_block(pa, entry_size);
		pte++;
	}

	return true;
}

/**
 * Updates the page table from the root to map the given address range to a
 * physical range using the provided (architecture-specific) attributes. Or if
 * MAP_FLAG_UNMAP is set, unmap the given range instead.
 */
static bool mm_map_root(struct mm_ptable *t, ptable_addr_t begin,
			ptable_addr_t end, uint64_t attrs, uint8_t root_level,
			int flags, struct mpool *ppool)
{
	size_t root_table_size = mm_entry_size(root_level);
	struct mm_page_table *table =
		&mm_page_table_from_pa(t->root)[mm_index(begin, root_level)];

	while (begin < end) {
		if (!mm_map_level(begin, end, pa_init(begin), attrs, table,
				  root_level - 1, flags, ppool)) {
			return false;
		}
		begin = mm_start_of_next_block(begin, root_table_size);
		table++;
	}

	return true;
}

/**
 * Updates the given table such that the given physical address range is mapped
 * or not mapped into the address space with the architecture-agnostic mode
 * provided.
 */
static bool mm_ptable_identity_update(struct mm_ptable *t, paddr_t pa_begin,
				      paddr_t pa_end, int mode,
				      struct mpool *ppool)
{
	uint64_t attrs = arch_mm_mode_to_attrs(mode);
	int flags = (mode & MM_MODE_NOINVALIDATE ? MAP_FLAG_NOBBM : 0) |
		    (mode & MM_MODE_STAGE1 ? MAP_FLAG_STAGE1 : 0) |
		    (mode & MM_MODE_INVALID && mode & MM_MODE_UNOWNED
			     ? MAP_FLAG_UNMAP
			     : 0);
	uint8_t root_level = arch_mm_max_level(mode) + 1;
	ptable_addr_t ptable_end =
		arch_mm_root_table_count(mode) * mm_entry_size(root_level);
	ptable_addr_t end = mm_round_up_to_page(pa_addr(pa_end));
	ptable_addr_t begin = pa_addr(arch_mm_clear_pa(pa_begin));

	/*
	 * TODO: replace with assertions that the max level will be greater than
	 * 0 and less than 255 so wrapping will not be a problem and will not
	 * lead to subsequent overflows.
	 */
	if (root_level == 0 || root_level == 1) {
		return false;
	}

	/* Cap end to stay within the bounds of the page table. */
	if (end > ptable_end) {
		end = ptable_end;
	}

	/*
	 * Do it in two steps to prevent leaving the table in a halfway updated
	 * state. In such a two-step implementation, the table may be left with
	 * extra internal tables, but no different mapping on failure.
	 */
	if (!mm_map_root(t, begin, end, attrs, root_level, flags, ppool) ||
	    !mm_map_root(t, begin, end, attrs, root_level,
			 flags | MAP_FLAG_COMMIT, ppool)) {
		return false;
	}

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
				   paddr_t pa_end, int mode,
				   struct mpool *ppool)
{
	return mm_ptable_identity_update(t, pa_begin, pa_end, mode, ppool);
}

/**
 * Updates the given table such that the given physical address range is not
 * mapped into the address space.
 */
static bool mm_ptable_unmap(struct mm_ptable *t, paddr_t pa_begin,
			    paddr_t pa_end, int mode, struct mpool *ppool)
{
	return mm_ptable_identity_update(
		t, pa_begin, pa_end, mode | MM_MODE_UNOWNED | MM_MODE_INVALID,
		ppool);
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
					table->entries[i], level)),
				level - 1, max_level);
		}
	}
}

/**
 * Write the given table to the debug log.
 */
void mm_ptable_dump(struct mm_ptable *t, int mode)
{
	struct mm_page_table *tables = mm_page_table_from_pa(t->root);
	int max_level = arch_mm_max_level(mode);
	uint8_t root_table_count = arch_mm_root_table_count(mode);
	uint8_t i;
	for (i = 0; i < root_table_count; ++i) {
		mm_dump_table_recursive(&tables[i], max_level, max_level);
	}
}

/**
 * Given that `entry` is a subtable but its entries are all absent, return the
 * absent entry with which it can be replaced. Note that `entry` will no longer
 * be valid after calling this function as the subtable will have been freed.
 */
static pte_t mm_table_pte_to_absent(pte_t entry, uint8_t level,
				    struct mpool *ppool)
{
	struct mm_page_table *table =
		mm_page_table_from_pa(arch_mm_table_from_pte(entry, level));

	/*
	 * Free the subtable. This is safe to do directly (rather than
	 * using mm_free_page_pte) because we know by this point that it
	 * doesn't have any subtables of its own.
	 */
	mpool_free(ppool, table);

	/* Replace subtable with a single absent entry. */
	return arch_mm_absent_pte(level);
}

/**
 * Given that `entry` is a subtable and its entries are all identical, return
 * the single block entry with which it can be replaced if possible. Note that
 * `entry` will no longer be valid after calling this function as the subtable
 * may have been freed.
 */
static pte_t mm_table_pte_to_block(pte_t entry, uint8_t level,
				   struct mpool *ppool)
{
	struct mm_page_table *table;
	uint64_t block_attrs;
	uint64_t table_attrs;
	uint64_t combined_attrs;
	paddr_t block_address;

	if (!arch_mm_is_block_allowed(level)) {
		return entry;
	}

	table = mm_page_table_from_pa(arch_mm_table_from_pte(entry, level));

	/* Replace subtable with a single block, with equivalent attributes. */
	block_attrs = arch_mm_pte_attrs(table->entries[0], level - 1);
	table_attrs = arch_mm_pte_attrs(entry, level);
	combined_attrs =
		arch_mm_combine_table_entry_attrs(table_attrs, block_attrs);
	block_address = arch_mm_block_from_pte(table->entries[0], level - 1);

	/* Free the subtable. */
	mpool_free(ppool, table);

	/*
	 * We can assume that the block is aligned properly because all virtual
	 * addresses are aligned by definition, and we have a 1-1 mapping from
	 * virtual to physical addresses.
	 */
	return arch_mm_block_pte(level, block_address, combined_attrs);
}

/**
 * Defragment the given ptable entry by recursively replacing any tables with
 * block or absent entries where possible.
 */
static pte_t mm_ptable_defrag_entry(pte_t entry, uint8_t level,
				    struct mpool *ppool)
{
	struct mm_page_table *table;
	uint64_t i;
	uint64_t attrs;
	bool identical_blocks_so_far = true;
	bool all_absent_so_far = true;

	if (!arch_mm_pte_is_table(entry, level)) {
		return entry;
	}

	table = mm_page_table_from_pa(arch_mm_table_from_pte(entry, level));

	/*
	 * Check if all entries are blocks with the same flags or are all
	 * absent.
	 */
	attrs = arch_mm_pte_attrs(table->entries[0], level);
	for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
		/*
		 * First try to defrag the entry, in case it is a subtable.
		 */
		table->entries[i] = mm_ptable_defrag_entry(table->entries[i],
							   level - 1, ppool);

		if (arch_mm_pte_is_present(table->entries[i], level - 1)) {
			all_absent_so_far = false;
		}

		/*
		 * If the entry is a block, check that the flags are the same as
		 * what we have so far.
		 */
		if (!arch_mm_pte_is_block(table->entries[i], level - 1) ||
		    arch_mm_pte_attrs(table->entries[i], level) != attrs) {
			identical_blocks_so_far = false;
		}
	}
	if (identical_blocks_so_far) {
		return mm_table_pte_to_block(entry, level, ppool);
	}
	if (all_absent_so_far) {
		return mm_table_pte_to_absent(entry, level, ppool);
	}
	return entry;
}

/**
 * Defragments the given page table by converting page table references to
 * blocks whenever possible.
 */
void mm_ptable_defrag(struct mm_ptable *t, int mode, struct mpool *ppool)
{
	struct mm_page_table *tables = mm_page_table_from_pa(t->root);
	uint8_t level = arch_mm_max_level(mode);
	uint8_t root_table_count = arch_mm_root_table_count(mode);
	uint8_t i;
	uint64_t j;

	/*
	 * Loop through each entry in the table. If it points to another table,
	 * check if that table can be replaced by a block or an absent entry.
	 */
	for (i = 0; i < root_table_count; ++i) {
		for (j = 0; j < MM_PTE_PER_PAGE; ++j) {
			tables[i].entries[j] = mm_ptable_defrag_entry(
				tables[i].entries[j], level, ppool);
		}
	}
}

/**
 * Determines if the given address is valid in the address space of the given
 * page table by recursively traversing all levels of the page table.
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

	if (!arch_mm_pte_is_valid(pte, level)) {
		return false;
	}

	if (arch_mm_pte_is_table(pte, level)) {
		return mm_is_mapped_recursive(
			mm_page_table_from_pa(
				arch_mm_table_from_pte(pte, level)),
			addr, level - 1);
	}

	/* The entry is a valid block. */
	return true;
}

/**
 * Determines if the given address is valid in the address space of the given
 * page table.
 */
static bool mm_ptable_is_mapped(struct mm_ptable *t, ptable_addr_t addr,
				int mode)
{
	struct mm_page_table *tables = mm_page_table_from_pa(t->root);
	uint8_t level = arch_mm_max_level(mode);
	size_t index;

	addr = mm_round_down_to_page(addr);
	index = mm_index(addr, level + 1);

	if (index >= arch_mm_root_table_count(mode)) {
		return false;
	}

	return mm_is_mapped_recursive(&tables[index], addr, level);
}

/**
 * Initialises the given page table.
 */
bool mm_ptable_init(struct mm_ptable *t, int mode, struct mpool *ppool)
{
	uint8_t i;
	size_t j;
	struct mm_page_table *tables;
	uint8_t root_table_count = arch_mm_root_table_count(mode);

	tables = mm_alloc_page_tables(root_table_count, ppool);
	if (tables == NULL) {
		return false;
	}

	for (i = 0; i < root_table_count; i++) {
		for (j = 0; j < MM_PTE_PER_PAGE; j++) {
			tables[i].entries[j] =
				arch_mm_absent_pte(arch_mm_max_level(mode));
		}
	}

	/* TODO: halloc could return a virtual or physical address if mm not
	 * enabled? */
	t->root = pa_init((uintpaddr_t)tables);

	return true;
}

/**
 * Frees all memory associated with the give page table.
 */
void mm_ptable_fini(struct mm_ptable *t, int mode, struct mpool *ppool)
{
	struct mm_page_table *tables = mm_page_table_from_pa(t->root);
	uint8_t level = arch_mm_max_level(mode);
	uint8_t root_table_count = arch_mm_root_table_count(mode);
	uint8_t i;
	uint64_t j;

	for (i = 0; i < root_table_count; ++i) {
		for (j = 0; j < MM_PTE_PER_PAGE; ++j) {
			mm_free_page_pte(tables[i].entries[j], level, ppool);
		}
	}

	mpool_add_chunk(ppool, tables,
			sizeof(struct mm_page_table) * root_table_count);
}

/**
 * Updates a VM's page table such that the given physical address range is
 * mapped in the address space at the corresponding address range in the
 * architecture-agnostic mode provided.
 */
bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
			int mode, ipaddr_t *ipa, struct mpool *ppool)
{
	bool success = mm_ptable_identity_map(t, begin, end,
					      mode & ~MM_MODE_STAGE1, ppool);

	if (success && ipa != NULL) {
		*ipa = ipa_from_pa(begin);
	}

	return success;
}

/**
 * Updates the VM's table such that the given physical address range is not
 * mapped in the address space.
 */
bool mm_vm_unmap(struct mm_ptable *t, paddr_t begin, paddr_t end, int mode,
		 struct mpool *ppool)
{
	return mm_ptable_unmap(t, begin, end, mode & ~MM_MODE_STAGE1, ppool);
}

/**
 * Unmaps the hypervisor pages from the given page table.
 */
bool mm_vm_unmap_hypervisor(struct mm_ptable *t, int mode, struct mpool *ppool)
{
	/* TODO: If we add pages dynamically, they must be included here too. */
	return mm_vm_unmap(t, layout_text_begin(), layout_text_end(), mode,
			   ppool) &&
	       mm_vm_unmap(t, layout_rodata_begin(), layout_rodata_end(), mode,
			   ppool) &&
	       mm_vm_unmap(t, layout_data_begin(), layout_data_end(), mode,
			   ppool);
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
 * Updates the hypervisor page table such that the given physical address range
 * is mapped into the address space at the corresponding address range in the
 * architecture-agnostic mode provided.
 */
void *mm_identity_map(paddr_t begin, paddr_t end, int mode, struct mpool *ppool)
{
	if (mm_ptable_identity_map(&ptable, begin, end, mode | MM_MODE_STAGE1,
				   ppool)) {
		return ptr_from_va(va_from_pa(begin));
	}

	return NULL;
}

/**
 * Updates the hypervisor table such that the given physical address range is
 * not mapped in the address space.
 */
bool mm_unmap(paddr_t begin, paddr_t end, int mode, struct mpool *ppool)
{
	return mm_ptable_unmap(&ptable, begin, end, mode | MM_MODE_STAGE1,
			       ppool);
}

/**
 * Initialises memory management for the hypervisor itself.
 */
bool mm_init(struct mpool *ppool)
{
	dlog_nosync("text: 0x%x - 0x%x\n", pa_addr(layout_text_begin()),
		    pa_addr(layout_text_end()));
	dlog_nosync("rodata: 0x%x - 0x%x\n", pa_addr(layout_rodata_begin()),
		    pa_addr(layout_rodata_end()));
	dlog_nosync("data: 0x%x - 0x%x\n", pa_addr(layout_data_begin()),
		    pa_addr(layout_data_end()));

	if (!mm_ptable_init(&ptable, MM_MODE_STAGE1, ppool)) {
		dlog_nosync("Unable to allocate memory for page table.\n");
		return false;
	}

	/* Map page for uart. */
	/* TODO: We may not want to map this. */
	mm_ptable_identity_map(
		&ptable, pa_init(PL011_BASE),
		pa_add(pa_init(PL011_BASE), PAGE_SIZE),
		MM_MODE_R | MM_MODE_W | MM_MODE_D | MM_MODE_STAGE1, ppool);

	/* Map each section. */
	mm_identity_map(layout_text_begin(), layout_text_end(), MM_MODE_X,
			ppool);

	mm_identity_map(layout_rodata_begin(), layout_rodata_end(), MM_MODE_R,
			ppool);

	mm_identity_map(layout_data_begin(), layout_data_end(),
			MM_MODE_R | MM_MODE_W, ppool);

	return arch_mm_init(ptable.root, true);
}

bool mm_cpu_init(void)
{
	return arch_mm_init(ptable.root, false);
}

/**
 * Defragments the hypervisor page table.
 */
void mm_defrag(struct mpool *ppool)
{
	mm_ptable_defrag(&ptable, MM_MODE_STAGE1, ppool);
}
