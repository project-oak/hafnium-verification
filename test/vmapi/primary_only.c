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

#include <stdalign.h>

#include "hf/arch/vm/power_mgmt.h"

#include "hf/spinlock.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

TEST(hf_vm_get_count, no_secondary_vms)
{
	EXPECT_EQ(hf_vm_get_count(), 1);
}

TEST(hf_vcpu_get_count, primary_has_at_least_one)
{
	EXPECT_GE(hf_vcpu_get_count(0), 0);
}

TEST(hf_vcpu_get_count, no_secondary_vms)
{
	EXPECT_EQ(hf_vcpu_get_count(1), -1);
}

TEST(hf_vcpu_get_count, large_invalid_vm_index)
{
	EXPECT_EQ(hf_vcpu_get_count(0xffffffff), -1);
}

TEST(hf_vcpu_run, cannot_run_primary)
{
	struct hf_vcpu_run_return res = hf_vcpu_run(HF_PRIMARY_VM_ID, 0);
	EXPECT_EQ(res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
}

TEST(hf_vcpu_run, cannot_run_absent_secondary)
{
	struct hf_vcpu_run_return res = hf_vcpu_run(1, 0);
	EXPECT_EQ(res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
}

/**
 * Releases the lock passed in.
 */
static void vm_cpu_entry(uintptr_t arg)
{
	struct spinlock *lock = (struct spinlock *)arg;

	dlog("Second CPU started.\n");
	sl_unlock(lock);
}

TEST(cpus, start)
{
	struct spinlock lock = SPINLOCK_INIT;
	alignas(4096) static char other_stack[4096];

	/* Start secondary while holding lock. */
	sl_lock(&lock);
	EXPECT_EQ(cpu_start(1, other_stack, sizeof(other_stack), vm_cpu_entry,
			    (uintptr_t)&lock),
		  true);

	/* Wait for CPU to release the lock. */
	sl_lock(&lock);
}
