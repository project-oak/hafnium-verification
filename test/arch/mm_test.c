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

#include "hf/arch/mm.h"

#include "hftest.h"

/** There must be at least two levels in the page table.  */
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
	int mode = MM_MODE_STAGE1;
	uint8_t max_level = arch_mm_max_level(mode);
	EXPECT_GE(max_level, MAX_LEVEL_LOWER_BOUND);
	EXPECT_LE(max_level, MAX_LEVEL_UPPER_BOUND);
}

/* TODO: initialize arch_mm and check max level of stage-2. */

/**
 * A block is present and mutually exclusive from a table.
 */
#define LEVEL_TEST(lvl)                                                      \
	TEST(arch_mm, block_properties_level##lvl)                           \
	{                                                                    \
		uint8_t level = lvl;                                         \
		uint64_t attrs = arch_mm_mode_to_attrs(0);                   \
		pte_t block_pte;                                             \
                                                                             \
		/* Test doesn't apply if a block is not allowed. */          \
		if (!arch_mm_is_block_allowed(level)) {                      \
			return;                                              \
		}                                                            \
                                                                             \
		block_pte = arch_mm_block_pte(level, pa_init(0x12345678000), \
					      attrs);                        \
                                                                             \
		EXPECT_TRUE(arch_mm_pte_is_present(block_pte, level));       \
		EXPECT_TRUE(arch_mm_pte_is_block(block_pte, level));         \
		EXPECT_FALSE(arch_mm_pte_is_table(block_pte, level));        \
	}
EXPAND_LEVEL_TESTS
#undef LEVEL_TEST
