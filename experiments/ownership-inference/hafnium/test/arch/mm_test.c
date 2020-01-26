/*
 * Copyright 2018 The Hafnium Authors.
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

#include "hf/arch/mm.h"

#include "test/hftest.h"

/** There must be at least two levels in the page table. */
#define MAX_LEVEL_LOWER_BOUND 1

/**
 * This is the number of levels that are tested and is constrained as it
 * controls the depth of recursion in the memory management code.
 */
#define MAX_LEVEL_UPPER_BOUND 3

/** X macro to expand tests for all levels. */
#define EXPAND_LEVEL_TESTS \
	LEVEL_TEST(0)      \
	LEVEL_TEST(1)      \
	LEVEL_TEST(2)      \
	LEVEL_TEST(3)

/* TODO: work out how to run these test against the host fake arch. */

/**
 * A block must be allowed at level 0 as this is the level which represents
 * pages.
 */
TEST(arch_mm, block_allowed_at_level0)
{
	ASSERT_TRUE(arch_mm_is_block_allowed(0));
}

/**
 * The maximum level must be within acceptable bounds.
 */
TEST(arch_mm, max_level_stage1)
{
	uint8_t max_level = arch_mm_stage1_max_level();
	EXPECT_GE(max_level, MAX_LEVEL_LOWER_BOUND);
	EXPECT_LE(max_level, MAX_LEVEL_UPPER_BOUND);
}

/* TODO: initialize arch_mm and check max level of stage-2. */

/**
 * An absent entry is not present, valid, a block nor a table.
 */
#define LEVEL_TEST(lvl)                                                  \
	TEST(arch_mm, absent_properties_level##lvl)                      \
	{                                                                \
		uint8_t level = lvl;                                     \
		pte_t absent_pte;                                        \
                                                                         \
		absent_pte = arch_mm_absent_pte(level);                  \
                                                                         \
		EXPECT_FALSE(arch_mm_pte_is_present(absent_pte, level)); \
		EXPECT_FALSE(arch_mm_pte_is_valid(absent_pte, level));   \
		EXPECT_FALSE(arch_mm_pte_is_block(absent_pte, level));   \
		EXPECT_FALSE(arch_mm_pte_is_table(absent_pte, level));   \
	}
EXPAND_LEVEL_TESTS
#undef LEVEL_TEST

/**
 * An invalid block is present and mutually exclusive from a table.
 */
#define LEVEL_TEST(lvl)                                                       \
	TEST(arch_mm, invalid_block_properties_level##lvl)                    \
	{                                                                     \
		uint8_t level = lvl;                                          \
		uint64_t attrs =                                              \
			arch_mm_mode_to_stage2_attrs(MM_MODE_INVALID);        \
		pte_t block_pte;                                              \
                                                                              \
		/* Test doesn't apply if a block is not allowed. */           \
		if (!arch_mm_is_block_allowed(level)) {                       \
			return;                                               \
		}                                                             \
                                                                              \
		block_pte = arch_mm_block_pte(level, pa_init(PAGE_SIZE * 19), \
					      attrs);                         \
                                                                              \
		EXPECT_TRUE(arch_mm_pte_is_present(block_pte, level));        \
		EXPECT_FALSE(arch_mm_pte_is_valid(block_pte, level));         \
		EXPECT_TRUE(arch_mm_pte_is_block(block_pte, level));          \
		EXPECT_FALSE(arch_mm_pte_is_table(block_pte, level));         \
	}
EXPAND_LEVEL_TESTS
#undef LEVEL_TEST

/**
 * A valid block is present and mutually exclusive from a table.
 */
#define LEVEL_TEST(lvl)                                                \
	TEST(arch_mm, valid_block_properties_level##lvl)               \
	{                                                              \
		uint8_t level = lvl;                                   \
		uint64_t attrs = arch_mm_mode_to_stage2_attrs(0);      \
		pte_t block_pte;                                       \
                                                                       \
		/* Test doesn't apply if a block is not allowed. */    \
		if (!arch_mm_is_block_allowed(level)) {                \
			return;                                        \
		}                                                      \
                                                                       \
		block_pte = arch_mm_block_pte(                         \
			level, pa_init(PAGE_SIZE * 12345678), attrs);  \
                                                                       \
		EXPECT_TRUE(arch_mm_pte_is_present(block_pte, level)); \
		EXPECT_TRUE(arch_mm_pte_is_valid(block_pte, level));   \
		EXPECT_TRUE(arch_mm_pte_is_block(block_pte, level));   \
		EXPECT_FALSE(arch_mm_pte_is_table(block_pte, level));  \
	}
EXPAND_LEVEL_TESTS
#undef LEVEL_TEST

/**
 * A table is present, valid and mutually exclusive from a block.
 */
#define LEVEL_TEST(lvl)                                                        \
	TEST(arch_mm, table_properties_level##lvl)                             \
	{                                                                      \
		uint8_t level = lvl;                                           \
		pte_t table_pte;                                               \
                                                                               \
		/* Test doesn't apply to level 0 as there can't be a table. */ \
		if (level == 0) {                                              \
			return;                                                \
		}                                                              \
                                                                               \
		table_pte = arch_mm_table_pte(level,                           \
					      pa_init(PAGE_SIZE * 999999999)); \
                                                                               \
		EXPECT_TRUE(arch_mm_pte_is_present(table_pte, level));         \
		EXPECT_TRUE(arch_mm_pte_is_valid(table_pte, level));           \
		EXPECT_FALSE(arch_mm_pte_is_block(table_pte, level));          \
		EXPECT_TRUE(arch_mm_pte_is_table(table_pte, level));           \
	}
EXPAND_LEVEL_TESTS
#undef LEVEL_TEST

/**
 * The address and attributes of a block must be preserved when encoding and
 * decoding.
 */
#define LEVEL_TEST(lvl)                                                      \
	TEST(arch_mm, block_addr_and_attrs_preserved_level##lvl)             \
	{                                                                    \
		uint8_t level = lvl;                                         \
		paddr_t addr;                                                \
		uint64_t attrs;                                              \
		pte_t block_pte;                                             \
                                                                             \
		/* Test doesn't apply if a block is not allowed. */          \
		if (!arch_mm_is_block_allowed(level)) {                      \
			return;                                              \
		}                                                            \
                                                                             \
		addr = pa_init(0);                                           \
		attrs = arch_mm_mode_to_stage2_attrs(0);                     \
		block_pte = arch_mm_block_pte(level, addr, attrs);           \
		EXPECT_EQ(arch_mm_pte_attrs(block_pte, level), attrs);       \
		EXPECT_EQ(pa_addr(arch_mm_block_from_pte(block_pte, level)), \
			  pa_addr(addr));                                    \
                                                                             \
		addr = pa_init(PAGE_SIZE * 17);                              \
		attrs = arch_mm_mode_to_stage2_attrs(MM_MODE_INVALID);       \
		block_pte = arch_mm_block_pte(level, addr, attrs);           \
		EXPECT_EQ(arch_mm_pte_attrs(block_pte, level), attrs);       \
		EXPECT_EQ(pa_addr(arch_mm_block_from_pte(block_pte, level)), \
			  pa_addr(addr));                                    \
                                                                             \
		addr = pa_init(PAGE_SIZE * 500);                             \
		attrs = arch_mm_mode_to_stage2_attrs(MM_MODE_R | MM_MODE_W); \
		block_pte = arch_mm_block_pte(level, addr, attrs);           \
		EXPECT_EQ(arch_mm_pte_attrs(block_pte, level), attrs);       \
		EXPECT_EQ(pa_addr(arch_mm_block_from_pte(block_pte, level)), \
			  pa_addr(addr));                                    \
	}
EXPAND_LEVEL_TESTS
#undef LEVEL_TEST
