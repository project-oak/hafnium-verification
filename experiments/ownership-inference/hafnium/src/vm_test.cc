/*
 * Copyright 2019 The Hafnium Authors.
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

#include <gmock/gmock.h>

extern "C" {
#include "hf/mpool.h"
#include "hf/vm.h"
}

#include <memory>
#include <span>
#include <vector>

#include "mm_test.hh"

namespace
{
using namespace ::std::placeholders;

using ::testing::AllOf;
using ::testing::Each;
using ::testing::SizeIs;

using struct_vm = struct vm;

constexpr size_t TEST_HEAP_SIZE = PAGE_SIZE * 16;
const int TOP_LEVEL = arch_mm_stage2_max_level();

class vm : public ::testing::Test
{
	void SetUp() override
	{
		/*
		 * TODO: replace with direct use of stdlib allocator so
		 * sanitizers are more effective.
		 */
		test_heap = std::make_unique<uint8_t[]>(TEST_HEAP_SIZE);
		mpool_init(&ppool, sizeof(struct mm_page_table));
		mpool_add_chunk(&ppool, test_heap.get(), TEST_HEAP_SIZE);
	}

	std::unique_ptr<uint8_t[]> test_heap;

       protected:
	struct mpool ppool;
};

/**
 * If nothing is mapped, unmapping the hypervisor has no effect.
 */
TEST_F(vm, vm_unmap_hypervisor_not_mapped)
{
	struct_vm *vm;
	struct vm_locked vm_locked;

	EXPECT_TRUE(vm_init_next(1, &ppool, &vm));
	vm_locked = vm_lock(vm);
	ASSERT_TRUE(mm_vm_init(&vm->ptable, &ppool));
	EXPECT_TRUE(vm_unmap_hypervisor(vm_locked, &ppool));
	EXPECT_THAT(
		mm_test::get_ptable(vm->ptable),
		AllOf(SizeIs(4), Each(Each(arch_mm_absent_pte(TOP_LEVEL)))));
	mm_vm_fini(&vm->ptable, &ppool);
	vm_unlock(&vm_locked);
}

} /* namespace */
