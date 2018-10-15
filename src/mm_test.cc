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
constexpr size_t ENTRY_COUNT = PAGE_SIZE / sizeof(pte_t);
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
 * Fill a ptable with absent entries.
 */
void init_absent(pte_t *table)
{
	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		table[i] = ABSENT_ENTRY;
	}
}

/**
 * Fill a ptable with block entries.
 */
void init_blocks(pte_t *table, int level, paddr_t start_address, uint64_t attrs)
{
	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		table[i] = arch_mm_block_pte(
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

	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_absent(table);
	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	mm_ptable_defrag(&ptable, 0);

	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(table[i], Eq(ABSENT_ENTRY)) << "i=" << i;
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

	pte_t *subtable_a = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *subtable_aa = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *subtable_b = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_absent(subtable_a);
	init_absent(subtable_aa);
	init_absent(subtable_b);
	init_absent(table);

	subtable_a[3] = arch_mm_table_pte(TOP_LEVEL - 1,
					  pa_init((uintpaddr_t)subtable_aa));
	table[0] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_a));
	table[5] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_b));

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	mm_ptable_defrag(&ptable, 0);

	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(table[i], Eq(ABSENT_ENTRY)) << "i=" << i;
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

	pte_t *subtable_a = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *subtable_aa = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *subtable_b = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_blocks(subtable_a, TOP_LEVEL - 1, pa_init(0), 0);
	init_blocks(subtable_aa, TOP_LEVEL - 2,
		    pa_init(3 * mm_entry_size(TOP_LEVEL - 1)), 0);
	init_blocks(subtable_b, TOP_LEVEL - 1,
		    pa_init(5 * mm_entry_size(TOP_LEVEL)), 0);
	init_blocks(table, TOP_LEVEL, pa_init(0), 0);

	subtable_a[3] = arch_mm_table_pte(TOP_LEVEL - 1,
					  pa_init((uintpaddr_t)subtable_aa));
	table[0] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_a));
	table[5] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_b));

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	mm_ptable_defrag(&ptable, 0);

	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		EXPECT_TRUE(arch_mm_pte_is_present(table[i], TOP_LEVEL))
			<< "i=" << i;
		EXPECT_TRUE(arch_mm_pte_is_block(table[i], TOP_LEVEL))
			<< "i=" << i;
		EXPECT_THAT(pa_addr(arch_mm_block_from_pte(table[i])),
			    Eq(i * mm_entry_size(TOP_LEVEL)))
			<< "i=" << i;
	}
}

/** If nothing is mapped, unmapping the hypervisor should have no effect. */
TEST(mm, ptable_unmap_hypervisor_not_mapped)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_absent(table);

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	EXPECT_TRUE(mm_ptable_unmap_hypervisor(&ptable, 0));

	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(table[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
}

/**
 * Unmapping everything should result in an empty page table with no subtables.
 */
TEST(mm, vm_unmap)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *subtable_a = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	pte_t *subtable_aa = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_absent(table);
	init_absent(subtable_a);
	init_absent(subtable_aa);

	subtable_aa[0] = arch_mm_block_pte(TOP_LEVEL - 2, pa_init(0), 0);
	subtable_a[0] = arch_mm_table_pte(TOP_LEVEL - 1,
					  pa_init((uintpaddr_t)subtable_aa));
	table[0] =
		arch_mm_table_pte(TOP_LEVEL, pa_init((uintpaddr_t)subtable_a));

	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	EXPECT_TRUE(mm_vm_unmap(&ptable, pa_init(0), pa_init(1), 0));

	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(table[i], Eq(ABSENT_ENTRY)) << "i=" << i;
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
	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_absent(table);
	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	/* Try mapping the first page. */
	ipaddr_t ipa = ipa_init(-1);
	EXPECT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), pa_init(PAGE_SIZE),
				       0, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0));

	/* Check that the first page is mapped, and nothing else. */
	for (uint64_t i = 1; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(table[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
	ASSERT_TRUE(arch_mm_pte_is_table(table[0], TOP_LEVEL));
	pte_t *subtable_a = (pte_t *)ptr_from_va(
		va_from_pa(arch_mm_table_from_pte(table[0])));
	for (uint64_t i = 1; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(subtable_a[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
	ASSERT_TRUE(arch_mm_pte_is_table(subtable_a[0], TOP_LEVEL - 1));
	pte_t *subtable_aa = (pte_t *)ptr_from_va(
		va_from_pa(arch_mm_table_from_pte(subtable_a[0])));
	for (uint64_t i = 1; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(subtable_aa[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
	EXPECT_TRUE(arch_mm_pte_is_block(subtable_aa[0], TOP_LEVEL - 2));
	EXPECT_THAT(pa_addr(arch_mm_block_from_pte(subtable_aa[0])), Eq(0));
}

/** Mapping a range that is already mapped should be a no-op. */
TEST(mm, vm_identity_map_already_mapped)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	/* Start with a full page table mapping everything. */
	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
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
	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		EXPECT_TRUE(arch_mm_pte_is_block(table[i], TOP_LEVEL))
			<< "i=" << i;
	}
}

/** Mapping a single page should result in just that page being mapped. */
TEST(mm, vm_identity_map_page)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	/* Start with an empty page table. */
	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_absent(table);
	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	/* Try mapping the first page. */
	ipaddr_t ipa = ipa_init(-1);
	EXPECT_TRUE(mm_vm_identity_map_page(&ptable, pa_init(0), 0, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0));

	/* Check that the first page is mapped, and nothing else. */
	for (uint64_t i = 1; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(table[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
	ASSERT_TRUE(arch_mm_pte_is_table(table[0], TOP_LEVEL));
	pte_t *subtable_a = (pte_t *)ptr_from_va(
		va_from_pa(arch_mm_table_from_pte(table[0])));
	for (uint64_t i = 1; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(subtable_a[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
	ASSERT_TRUE(arch_mm_pte_is_table(subtable_a[0], TOP_LEVEL - 1));
	pte_t *subtable_aa = (pte_t *)ptr_from_va(
		va_from_pa(arch_mm_table_from_pte(subtable_a[0])));
	for (uint64_t i = 1; i < ENTRY_COUNT; ++i) {
		EXPECT_THAT(subtable_aa[i], Eq(ABSENT_ENTRY)) << "i=" << i;
	}
	EXPECT_TRUE(arch_mm_pte_is_block(subtable_aa[0], TOP_LEVEL - 2));
	EXPECT_THAT(pa_addr(arch_mm_block_from_pte(subtable_aa[0])), Eq(0));
}

/** Mapping a page that is already mapped should be a no-op. */
TEST(mm, vm_identity_map_page_already_mapped)
{
	auto test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
	halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);

	/* Start with a full page table mapping everything. */
	pte_t *table = (pte_t *)halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	init_blocks(table, TOP_LEVEL, pa_init(0), 0);
	struct mm_ptable ptable;
	ptable.table = pa_init((uintpaddr_t)table);

	/* Try mapping the first page. */
	ipaddr_t ipa = ipa_init(-1);
	EXPECT_TRUE(mm_vm_identity_map_page(&ptable, pa_init(0), 0, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0));

	/*
	 * The table should still be full of blocks, with no subtables or
	 * anything else.
	 */
	for (uint64_t i = 0; i < ENTRY_COUNT; ++i) {
		EXPECT_TRUE(arch_mm_pte_is_block(table[i], TOP_LEVEL))
			<< "i=" << i;
	}
}

} /* namespace */
