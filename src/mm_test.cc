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

extern "C" {
#include "hf/mm.h"

#include "hf/arch/mm.h"

#include "hf/alloc.h"
}

#include <memory>

#include <gmock/gmock.h>

namespace
{
using ::testing::Eq;

constexpr size_t TEST_HEAP_SIZE = PAGE_SIZE * 10;
const int TOP_LEVEL = arch_mm_max_level(0);
const pte_t ABSENT_ENTRY = arch_mm_absent_pte(TOP_LEVEL);

/**
 * Calculates the size of the address space represented by a page table entry at
 * the given level.
 */
size_t mm_entry_size(int level)
{
	return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
}

/**
 * Get the page table from the physical address.
 */
struct mm_page_table *page_table_from_pa(paddr_t pa)
{
	return reinterpret_cast<struct mm_page_table *>(
		ptr_from_va(va_from_pa(pa)));
}

/**
 * Allocate a page table.
 */
struct mm_page_table *alloc_page_table()
{
	return reinterpret_cast<struct mm_page_table *>(halloc_aligned(
		sizeof(struct mm_page_table), alignof(struct mm_page_table)));
}

/**
 * Fill a ptable with absent entries.
 */
void init_absent(struct mm_page_table *table)
{
	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		table->entries[i] = ABSENT_ENTRY;
	}
}

/**
 * Fill a ptable with block entries.
 */
void init_blocks(struct mm_page_table *table, int level, paddr_t start_address,
		 uint64_t attrs)
{
	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		table->entries[i] = arch_mm_block_pte(
			level, pa_add(start_address, i * mm_entry_size(level)),
			attrs);
	}
}

/**
 * Defragging an entirely empty table should have no effect.
 */
TEST(mm, ptable_defrag_empty)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	struct mm_page_table *table = alloc_page_table();
	init_absent(table);
	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	mm_ptable_defrag(&ptable, 0);

	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_THAT(table->entries[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
}

/**
 * Defragging a table with some empty subtables (even nested) should result in
 * an empty table.
 */
TEST(mm, ptable_defrag_empty_subtables)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	struct mm_page_table *subtable_a = alloc_page_table();
	struct mm_page_table *subtable_aa = alloc_page_table();
	struct mm_page_table *subtable_b = alloc_page_table();
	struct mm_page_table *table = alloc_page_table();
	init_absent(subtable_a);
	init_absent(subtable_aa);
	init_absent(subtable_b);
	init_absent(table);

	subtable_a->entries[3] = arch_mm_table_pte(
		TOP_LEVEL - 1, pa_init((uintpaddr_t)subtable_aa));
	table->entries[0] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_a));
	table->entries[5] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_b));

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	mm_ptable_defrag(&ptable, 0);

	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_THAT(table->entries[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
}

/**
 * Any subtable with all blocks with the same attributes should be replaced
 * with a single block.
 */
TEST(mm, ptable_defrag_block_subtables)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	struct mm_page_table *subtable_a = alloc_page_table();
	struct mm_page_table *subtable_aa = alloc_page_table();
	struct mm_page_table *subtable_b = alloc_page_table();
	struct mm_page_table *table = alloc_page_table();
	init_blocks(subtable_a, TOP_LEVEL - 1, pa_init(0), 0);
	init_blocks(subtable_aa, TOP_LEVEL - 2,
		    pa_init(3 * mm_entry_size(TOP_LEVEL - 1)), 0);
	init_blocks(subtable_b, TOP_LEVEL - 1,
		    pa_init(5 * mm_entry_size(TOP_LEVEL)), 0);
	init_blocks(table, TOP_LEVEL, pa_init(0), 0);

	subtable_a->entries[3] = arch_mm_table_pte(
		TOP_LEVEL - 1, pa_init((uintpaddr_t)subtable_aa));
	table->entries[0] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_a));
	table->entries[5] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_b));

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	mm_ptable_defrag(&ptable, 0);

	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_TRUE(
			arch_mm_pte_is_present(table->entries[i], TOP_LEVEL))
			<< "i=" << i;
		EXPECT_TRUE(arch_mm_pte_is_block(table->entries[i], TOP_LEVEL))
			<< "i=" << i;
		EXPECT_THAT(pa_addr(arch_mm_block_from_pte(table->entries[i])),
			    Eq(i * mm_entry_size(TOP_LEVEL)))
			<< "i=" << i;
	}
}

/** If nothing is mapped, unmapping the hypervisor should have no effect. */
TEST(mm, ptable_unmap_hypervisor_not_mapped)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	struct mm_page_table *table = alloc_page_table();
	init_absent(table);

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	EXPECT_TRUE(mm_ptable_unmap_hypervisor(&ptable, 0));

	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_THAT(table->entries[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
}

/**
 * Unmapping everything should result in an empty page table with no subtables.
 */
TEST(mm, vm_unmap)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	struct mm_page_table *subtable_a = alloc_page_table();
	struct mm_page_table *subtable_aa = alloc_page_table();
	struct mm_page_table *table = alloc_page_table();
	init_absent(subtable_a);
	init_absent(subtable_aa);
	init_absent(table);

	subtable_aa->entries[0] =
		arch_mm_block_pte(TOP_LEVEL - 2, pa_init(0), 0);
	subtable_a->entries[0] = arch_mm_table_pte(
		TOP_LEVEL - 1, pa_init((uintpaddr_t)subtable_aa));
	table->entries[0] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_a));

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	EXPECT_TRUE(mm_vm_unmap(&ptable, pa_init(0), pa_init(1), 0));

	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_THAT(table->entries[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
}

/**
 * Mapping a range should result in just the corresponding pages being mapped.
 */
TEST(mm, vm_identity_map)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	/* Start with an empty page table. */
	struct mm_page_table *table = alloc_page_table();
	init_absent(table);
	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	/* Try mapping the first page. */
	ipaddr_t ipa = ipa_init(-1);
	EXPECT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), pa_init(PAGE_SIZE),
				       0, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0));

	/* Check that the first page is mapped, and nothing else. */
	for (uint64_t i = 1; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_THAT(table->entries[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
	ASSERT_TRUE(arch_mm_pte_is_table(table->entries[0], TOP_LEVEL));
	struct mm_page_table *subtable_a =
		page_table_from_pa(arch_mm_table_from_pte(table->entries[0]));
	for (uint64_t i = 1; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_THAT(subtable_a->entries[i], Eq(ABSENT_ENTRY))
			<< "i=" << i;
	}
	ASSERT_TRUE(
		arch_mm_pte_is_table(subtable_a->entries[0], TOP_LEVEL - 1));
	struct mm_page_table *subtable_aa = page_table_from_pa(
		arch_mm_table_from_pte(subtable_a->entries[0]));
	for (uint64_t i = 1; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_THAT(subtable_aa->entries[i], Eq(ABSENT_ENTRY))
			<< "i=" << i;
	}
	EXPECT_TRUE(
		arch_mm_pte_is_block(subtable_aa->entries[0], TOP_LEVEL - 2));
	EXPECT_THAT(pa_addr(arch_mm_block_from_pte(subtable_aa->entries[0])),
		    Eq(0));
}

/** Mapping a range that is already mapped should be a no-op. */
TEST(mm, vm_identity_map_already_mapped)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	/* Start with a full page table mapping everything. */
	struct mm_page_table *table = alloc_page_table();
	init_blocks(table, TOP_LEVEL, pa_init(0), 0);
	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	/* Try mapping the first page. */
	ipaddr_t ipa = ipa_init(-1);
	EXPECT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), pa_init(PAGE_SIZE),
				       0, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0));

	/*
	 * The table should still be full of blocks, with no subtables or
	 * anything else.
	 */
	for (uint64_t i = 0; i < MM_PTE_PER_PAGE; ++i) {
		EXPECT_TRUE(arch_mm_pte_is_block(table->entries[i], TOP_LEVEL))
			<< "i=" << i;
	}
}

} /* namespace */
