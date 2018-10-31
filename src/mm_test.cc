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

#include <limits>
#include <memory>
#include <span>
#include <vector>

#include <gmock/gmock.h>

namespace
{
using namespace ::std::placeholders;

using ::testing::AllOf;
using ::testing::Contains;
using ::testing::Each;
using ::testing::Eq;
using ::testing::SizeIs;
using ::testing::Truly;

constexpr size_t TEST_HEAP_SIZE = PAGE_SIZE * 16;
const int TOP_LEVEL = arch_mm_max_level(0);
const pte_t ABSENT_ENTRY = arch_mm_absent_pte(TOP_LEVEL);
const paddr_t VM_MEM_END = pa_init(0x200'0000'0000);

/**
 * Calculates the size of the address space represented by a page table entry at
 * the given level.
 */
size_t mm_entry_size(int level)
{
	return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
}

/**
 * Get an STL representation of the page table.
 */
std::span<pte_t, MM_PTE_PER_PAGE> get_table(paddr_t pa)
{
	auto table = reinterpret_cast<struct mm_page_table *>(
		ptr_from_va(va_from_pa(pa)));
	return std::span<pte_t>(table->entries, std::end(table->entries));
}

/**
 * Get an STL representation of the ptable.
 */
std::vector<std::span<pte_t, MM_PTE_PER_PAGE>> get_ptable(
	const struct mm_ptable &ptable, int mode)
{
	std::vector<std::span<pte_t, MM_PTE_PER_PAGE>> all;
	const uint8_t root_table_count = arch_mm_root_table_count(mode);
	for (uint8_t i = 0; i < root_table_count; ++i) {
		all.push_back(get_table(
			pa_add(ptable.root, i * sizeof(struct mm_page_table))));
	}
	return all;
}

class mm : public ::testing::Test
{
	void SetUp() override
	{
		/*
		 * TODO: replace with direct use of stdlib allocator so
		 * sanitizers are more effective.
		 */
		test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
		halloc_init((size_t)test_heap.get(), TEST_HEAP_SIZE);
	}

	std::unique_ptr<uint8_t[]> test_heap;
};

/**
 * A new table is initially empty.
 */
TEST_F(mm, ptable_init_empty)
{
	constexpr int mode = MM_MODE_STAGE1;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(1), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Each new concatenated table is initially empty.
 */
TEST_F(mm, ptable_init_concatenated_empty)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Only the first page is mapped with all others left absent.
 */
TEST_F(mm, map_first_page)
{
	constexpr int mode = 0;
	const paddr_t page_begin = pa_init(0);
	const paddr_t page_end = pa_add(page_begin, PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, page_begin, page_end, mode,
				       nullptr));

	auto tables = get_ptable(ptable, mode);
	EXPECT_THAT(tables, SizeIs(4));
	ASSERT_THAT(TOP_LEVEL, Eq(2));

	/* Check that the first page is mapped and nothing else. */
	EXPECT_THAT(std::span(tables).last(3), Each(Each(ABSENT_ENTRY)));

	auto table_l2 = tables.front();
	EXPECT_THAT(table_l2.subspan(1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table_l2[0], TOP_LEVEL));

	auto table_l1 = get_table(arch_mm_table_from_pte(table_l2[0]));
	EXPECT_THAT(table_l1.subspan(1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table_l1[0], TOP_LEVEL - 1));

	auto table_l0 = get_table(arch_mm_table_from_pte(table_l1[0]));
	EXPECT_THAT(table_l0.subspan(1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_block(table_l0[0], TOP_LEVEL - 2));
	EXPECT_THAT(pa_addr(arch_mm_block_from_pte(table_l0[0])),
		    Eq(pa_addr(page_begin)));

	mm_ptable_fini(&ptable, mode);
}

/**
 * The start address is rounded down and the end address is rounded up to page
 * boundaries.
 */
TEST_F(mm, map_round_to_page)
{
	constexpr int mode = 0;
	const paddr_t map_begin = pa_init(0x200'0000'0000 - PAGE_SIZE + 23);
	const paddr_t map_end = pa_add(map_begin, 268);
	ipaddr_t ipa = ipa_init(-1);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, map_begin, map_end, mode, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(pa_addr(map_begin)));

	auto tables = get_ptable(ptable, mode);
	EXPECT_THAT(tables, SizeIs(4));
	ASSERT_THAT(TOP_LEVEL, Eq(2));

	/* Check that the last page is mapped, and nothing else. */
	EXPECT_THAT(std::span(tables).first(3), Each(Each(ABSENT_ENTRY)));

	auto table_l2 = tables.back();
	EXPECT_THAT(table_l2.first(table_l2.size() - 1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table_l2.last(1)[0], TOP_LEVEL));

	auto table_l1 = get_table(arch_mm_table_from_pte(table_l2.last(1)[0]));
	EXPECT_THAT(table_l1.first(table_l1.size() - 1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table_l1.last(1)[0], TOP_LEVEL - 1));

	auto table_l0 = get_table(arch_mm_table_from_pte(table_l1.last(1)[0]));
	EXPECT_THAT(table_l0.first(table_l0.size() - 1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_block(table_l0.last(1)[0], TOP_LEVEL - 2));
	EXPECT_THAT(pa_addr(arch_mm_block_from_pte(table_l0.last(1)[0])),
		    Eq(0x200'0000'0000 - PAGE_SIZE));

	mm_ptable_fini(&ptable, mode);
}

/**
 * Map a two page range over the boundary of two tables.
 */
TEST_F(mm, map_across_tables)
{
	constexpr int mode = 0;
	const paddr_t map_begin = pa_init(0x80'0000'0000 - PAGE_SIZE);
	const paddr_t map_end = pa_add(map_begin, 2 * PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, map_begin, map_end, mode, nullptr));

	auto tables = get_ptable(ptable, mode);
	EXPECT_THAT(tables, SizeIs(4));
	EXPECT_THAT(std::span(tables).last(2), Each(Each(ABSENT_ENTRY)));
	ASSERT_THAT(TOP_LEVEL, Eq(2));

	/* Check only the last page of the first table is mapped. */
	auto table0_l2 = tables.front();
	EXPECT_THAT(table0_l2.first(table0_l2.size() - 1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table0_l2.last(1)[0], TOP_LEVEL));

	auto table0_l1 =
		get_table(arch_mm_table_from_pte(table0_l2.last(1)[0]));
	EXPECT_THAT(table0_l1.first(table0_l1.size() - 1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table0_l1.last(1)[0], TOP_LEVEL - 1));

	auto table0_l0 =
		get_table(arch_mm_table_from_pte(table0_l1.last(1)[0]));
	EXPECT_THAT(table0_l0.first(table0_l0.size() - 1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_block(table0_l0.last(1)[0], TOP_LEVEL - 2));
	EXPECT_THAT(pa_addr(arch_mm_block_from_pte(table0_l0.last(1)[0])),
		    Eq(pa_addr(map_begin)));

	/* Checl only the first page of the second table is mapped. */
	auto table1_l2 = tables[1];
	EXPECT_THAT(table1_l2.subspan(1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table1_l2[0], TOP_LEVEL));

	auto table1_l1 = get_table(arch_mm_table_from_pte(table1_l2[0]));
	EXPECT_THAT(table1_l1.subspan(1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_table(table1_l1[0], TOP_LEVEL - 1));

	auto table1_l0 = get_table(arch_mm_table_from_pte(table1_l1[0]));
	EXPECT_THAT(table1_l0.subspan(1), Each(ABSENT_ENTRY));
	ASSERT_TRUE(arch_mm_pte_is_block(table1_l0[0], TOP_LEVEL - 2));
	EXPECT_THAT(pa_addr(arch_mm_block_from_pte(table1_l0[0])),
		    Eq(pa_addr(pa_add(map_begin, PAGE_SIZE))));

	mm_ptable_fini(&ptable, mode);
}

/**
 * Mapping all of memory creates blocks at the highest level.
 */
TEST_F(mm, map_all_at_top_level)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	auto tables = get_ptable(ptable, mode);
	EXPECT_THAT(
		tables,
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	for (uint64_t i = 0; i < tables.size(); ++i) {
		for (uint64_t j = 0; j < MM_PTE_PER_PAGE; ++j) {
			EXPECT_THAT(
				pa_addr(arch_mm_block_from_pte(tables[i][j])),
				Eq((i * mm_entry_size(TOP_LEVEL + 1)) +
				   (j * mm_entry_size(TOP_LEVEL))))
				<< "i=" << i << " j=" << j;
		}
	}
	mm_ptable_fini(&ptable, mode);
}

/**
 * Map all memory then trying to map a page again doesn't introduce a special
 * mapping for that particular page.
 */
TEST_F(mm, map_already_mapped)
{
	constexpr int mode = 0;
	ipaddr_t ipa = ipa_init(-1);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), pa_init(PAGE_SIZE),
				       mode, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0));
	EXPECT_THAT(
		get_ptable(ptable, mode),
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Mapping a reverse range, i.e. the end comes before the start, is treated as
 * an empty range so no mappings are made.
 */
TEST_F(mm, map_reverse_range)
{
	constexpr int mode = 0;
	ipaddr_t ipa = ipa_init(-1);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0x1234'5678),
				       pa_init(0x5000), mode, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0x1234'5678));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Mapping a reverse range in the same page will map the page because the start
 * of the range is rounded down and the end is rounded up.
 *
 * This serves as a form of documentation of behaviour rather than a
 * requirement. Check whether any code relies on this before changing it.
 */
TEST_F(mm, map_reverse_range_quirk)
{
	constexpr int mode = 0;
	ipaddr_t ipa = ipa_init(-1);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(20), pa_init(10), mode,
				       &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(20));
	EXPECT_TRUE(mm_vm_is_mapped(&ptable, ipa, mode));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Mapping a range up to the maximum address causes the range end to wrap to
 * zero as it is rounded up to a page boundary meaning no memory is mapped.
 *
 * This serves as a form of documentation of behaviour rather than a
 * requirement. Check whether any code relies on this before changing it.
 */
TEST_F(mm, map_last_address_quirk)
{
	constexpr int mode = 0;
	ipaddr_t ipa = ipa_init(-1);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(
		&ptable, pa_init(0),
		pa_init(std::numeric_limits<uintpaddr_t>::max()), mode, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(0));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Mapping a range that goes beyond the available memory clamps to the available
 * range.
 */
TEST_F(mm, map_clamp_to_range)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0),
				       pa_init(0xf32'0000'0000'0000), mode,
				       nullptr));
	EXPECT_THAT(
		get_ptable(ptable, mode),
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Mapping a range outside of the available memory is ignored and doesn't alter
 * the page tables.
 */
TEST_F(mm, map_ignore_out_of_range)
{
	constexpr int mode = 0;
	ipaddr_t ipa = ipa_init(-1);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(
		&ptable, VM_MEM_END, pa_init(0xf0'0000'0000'0000), mode, &ipa));
	EXPECT_THAT(ipa_addr(ipa), Eq(pa_addr(VM_MEM_END)));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, 0);
}

/**
 * Map a single page and then map all of memory which replaces the single page
 * mapping with a higher level block mapping.
 */
TEST_F(mm, map_block_replaces_table)
{
	constexpr int mode = 0;
	const paddr_t page_begin = pa_init(34567 * PAGE_SIZE);
	const paddr_t page_end = pa_add(page_begin, PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, page_begin, page_end, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	EXPECT_THAT(
		get_ptable(ptable, mode),
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Map all memory at the top level, unmapping a page and remapping at a lower
 * level does not result in all memory being mapped at the top level again.
 */
TEST_F(mm, map_does_not_defrag)
{
	constexpr int mode = 0;
	const paddr_t page_begin = pa_init(12000 * PAGE_SIZE);
	const paddr_t page_end = pa_add(page_begin, PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, page_begin, page_end, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, page_begin, page_end, mode,
				       nullptr));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4),
			  Each(Each(Truly(std::bind(arch_mm_pte_is_present, _1,
						    TOP_LEVEL)))),
			  Contains(Contains(Truly(std::bind(
				  arch_mm_pte_is_block, _1, TOP_LEVEL)))),
			  Contains(Contains(Truly(std::bind(
				  arch_mm_pte_is_table, _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * If nothing is mapped, unmapping the hypervisor has no effect.
 */
TEST_F(mm, vm_unmap_hypervisor_not_mapped)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	EXPECT_TRUE(mm_vm_unmap_hypervisor(&ptable, mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * If range is not mapped, unmapping has no effect.
 */
TEST_F(mm, unmap_not_mapped)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	EXPECT_TRUE(
		mm_vm_unmap(&ptable, pa_init(12345), pa_init(987652), mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Unmapping everything should result in an empty page table with no subtables.
 */
TEST_F(mm, unmap_all)
{
	constexpr int mode = 0;
	const paddr_t l0_begin = pa_init(uintpaddr_t(524421) * PAGE_SIZE);
	const paddr_t l0_end = pa_add(l0_begin, 17 * PAGE_SIZE);
	const paddr_t l1_begin = pa_init(3 * mm_entry_size(1));
	const paddr_t l1_end = pa_add(l1_begin, 5 * mm_entry_size(1));
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, l0_begin, l0_end, mode, nullptr));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, l1_begin, l1_end, mode, nullptr));
	EXPECT_TRUE(mm_vm_unmap(&ptable, pa_init(0), VM_MEM_END, mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Unmap range is rounded to the containing pages.
 */
TEST_F(mm, unmap_round_to_page)
{
	constexpr int mode = 0;
	const paddr_t map_begin = pa_init(0x160'0000'0000 + PAGE_SIZE);
	const paddr_t map_end = pa_add(map_begin, PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, map_begin, map_end, mode, nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, pa_add(map_begin, 93),
				pa_add(map_begin, 99), mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Unmap a range that of page mappings that spans multiple concatenated tables.
 */
TEST_F(mm, unmap_across_tables)
{
	constexpr int mode = 0;
	const paddr_t map_begin = pa_init(0x180'0000'0000 - PAGE_SIZE);
	const paddr_t map_end = pa_add(map_begin, 2 * PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, map_begin, map_end, mode, nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, map_begin, map_end, mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Unmapping outside the range of memory had no effect.
 */
TEST_F(mm, unmap_out_of_range)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, VM_MEM_END, pa_init(0x4000'0000'0000),
				mode));
	EXPECT_THAT(
		get_ptable(ptable, mode),
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Unmapping a reverse range, i.e. the end comes before the start, is treated as
 * an empty range so no change is made.
 */
TEST_F(mm, unmap_reverse_range)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, pa_init(0x80'a000'0000), pa_init(27),
				mode));
	EXPECT_THAT(
		get_ptable(ptable, mode),
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Unmapping a reverse range in the same page will unmap the page because the
 * start of the range is rounded down and the end is rounded up.
 *
 * This serves as a form of documentation of behaviour rather than a
 * requirement. Check whether any code relies on this before changing it.
 */
TEST_F(mm, unmap_reverse_range_quirk)
{
	constexpr int mode = 0;
	const paddr_t page_begin = pa_init(0x180'0000'0000);
	const paddr_t page_end = pa_add(page_begin, PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, page_begin, page_end, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, pa_add(page_begin, 100),
				pa_add(page_begin, 50), mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Unmapping a range up to the maximum address causes the range end to wrap to
 * zero as it is rounded up to a page boundary meaning no change is made.
 *
 * This serves as a form of documentation of behaviour rather than a
 * requirement. Check whether any code relies on this before changing it.
 */
TEST_F(mm, unmap_last_address_quirk)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_unmap(
		&ptable, pa_init(0),
		pa_init(std::numeric_limits<uintpaddr_t>::max()), mode));
	EXPECT_THAT(
		get_ptable(ptable, mode),
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Mapping then unmapping a page does not defrag the table.
 */
TEST_F(mm, unmap_does_not_defrag)
{
	constexpr int mode = 0;
	const paddr_t l0_begin = pa_init(5555 * PAGE_SIZE);
	const paddr_t l0_end = pa_add(l0_begin, 13 * PAGE_SIZE);
	const paddr_t l1_begin = pa_init(666 * mm_entry_size(1));
	const paddr_t l1_end = pa_add(l1_begin, 5 * mm_entry_size(1));
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, l0_begin, l0_end, mode, nullptr));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, l1_begin, l1_end, mode, nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, l0_begin, l0_end, mode));
	ASSERT_TRUE(mm_vm_unmap(&ptable, l1_begin, l1_end, mode));
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, MM_MODE_STAGE1);
}

/**
 * Nothing is mapped in an empty table.
 */
TEST_F(mm, is_mapped_empty)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	EXPECT_FALSE(mm_vm_is_mapped(&ptable, ipa_init(0), mode));
	EXPECT_FALSE(mm_vm_is_mapped(&ptable, ipa_init(0x8123'2344), mode));
	EXPECT_FALSE(mm_vm_is_mapped(&ptable, ipa_init(0x1e0'0000'0073), mode));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Everything is mapped in a full table.
 */
TEST_F(mm, is_mapped_all)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	EXPECT_TRUE(mm_vm_is_mapped(&ptable, ipa_init(0), mode));
	EXPECT_TRUE(mm_vm_is_mapped(&ptable, ipa_init(0xf247'a7b3), mode));
	EXPECT_TRUE(mm_vm_is_mapped(&ptable, ipa_init(0x1ff'7bfa'983b), mode));
	mm_ptable_fini(&ptable, mode);
}

/**
 * A page is mapped for the range [begin, end).
 */
TEST_F(mm, is_mapped_page)
{
	constexpr int mode = 0;
	const paddr_t page_begin = pa_init(0x100'0000'0000);
	const paddr_t page_end = pa_add(page_begin, PAGE_SIZE);
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, page_begin, page_end, mode,
				       nullptr));
	EXPECT_TRUE(mm_vm_is_mapped(&ptable, ipa_from_pa(page_begin), mode));
	EXPECT_TRUE(mm_vm_is_mapped(
		&ptable, ipa_from_pa(pa_add(page_begin, 127)), mode));
	EXPECT_FALSE(mm_vm_is_mapped(&ptable, ipa_from_pa(page_end), mode));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Everything out of range is not mapped.
 */
TEST_F(mm, is_mapped_out_of_range)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	EXPECT_FALSE(mm_vm_is_mapped(&ptable, ipa_from_pa(VM_MEM_END), mode));
	EXPECT_FALSE(
		mm_vm_is_mapped(&ptable, ipa_init(0x1000'adb7'8123), mode));
	EXPECT_FALSE(mm_vm_is_mapped(
		&ptable, ipa_init(std::numeric_limits<uintpaddr_t>::max()),
		mode));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Defragging an entirely empty table has no effect.
 */
TEST_F(mm, defrag_empty)
{
	constexpr int mode = 0;
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	mm_ptable_defrag(&ptable, mode);
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Defragging a table with some empty subtables (even nested) results in
 * an empty table.
 */
TEST_F(mm, defrag_empty_subtables)
{
	constexpr int mode = 0;
	const paddr_t l0_begin = pa_init(120000 * PAGE_SIZE);
	const paddr_t l0_end = pa_add(l0_begin, PAGE_SIZE);
	const paddr_t l1_begin = pa_init(3 * mm_entry_size(1));
	const paddr_t l1_end = pa_add(l1_begin, 5 * mm_entry_size(1));
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, l0_begin, l0_end, mode, nullptr));
	ASSERT_TRUE(
		mm_vm_identity_map(&ptable, l0_begin, l0_end, mode, nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, l0_begin, l0_end, mode));
	ASSERT_TRUE(mm_vm_unmap(&ptable, l1_begin, l1_end, mode));
	mm_ptable_defrag(&ptable, 0);
	EXPECT_THAT(get_ptable(ptable, mode),
		    AllOf(SizeIs(4), Each(Each(ABSENT_ENTRY))));
	mm_ptable_fini(&ptable, mode);
}

/**
 * Any subtable with all blocks with the same attributes should be replaced
 * with a single block.
 */
TEST_F(mm, defrag_block_subtables)
{
	constexpr int mode = 0;
	const paddr_t begin = pa_init(39456 * mm_entry_size(1));
	const paddr_t middle = pa_add(begin, 67 * PAGE_SIZE);
	const paddr_t end = pa_add(begin, 4 * mm_entry_size(1));
	struct mm_ptable ptable;
	ASSERT_TRUE(mm_ptable_init(&ptable, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, pa_init(0), VM_MEM_END, mode,
				       nullptr));
	ASSERT_TRUE(mm_vm_unmap(&ptable, begin, end, mode));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, begin, middle, mode, nullptr));
	ASSERT_TRUE(mm_vm_identity_map(&ptable, middle, end, mode, nullptr));
	mm_ptable_defrag(&ptable, 0);
	EXPECT_THAT(
		get_ptable(ptable, mode),
		AllOf(SizeIs(4), Each(Each(Truly(std::bind(arch_mm_pte_is_block,
							   _1, TOP_LEVEL))))));
	mm_ptable_fini(&ptable, mode);
}

} /* namespace */
