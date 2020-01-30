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

#include <stdalign.h>

#include "hf/arch/vm/power_mgmt.h"

#include "hf/spinlock.h"

#include "vmapi/hf/call.h"

#include "test/hftest.h"
#include "test/vmapi/spci.h"

/*
 * TODO: Some of these tests are duplicated between 'primary_only' and
 * 'primary_with_secondaries'. Move them to a common place consider running
 * them inside secondary VMs too.
 */

/**
 * Confirms the primary VM has the primary ID.
 */
TEST(hf_vm_get_id, primary_has_primary_id)
{
	EXPECT_EQ(hf_vm_get_id(), HF_PRIMARY_VM_ID);
}

/**
 * Confirm there is only the primary VM.
 */
TEST(hf_vm_get_count, no_secondary_vms)
{
	EXPECT_EQ(hf_vm_get_count(), 1);
}

/**
 * Confirm the primary has at least one vCPU.
 */
TEST(hf_vcpu_get_count, primary_has_at_least_one)
{
	EXPECT_GE(hf_vcpu_get_count(HF_PRIMARY_VM_ID), 0);
}

/**
 * Confirm an error is returned when getting the vCPU count of a non-existent
 * VM.
 */
TEST(hf_vcpu_get_count, no_secondary_vms)
{
	EXPECT_EQ(hf_vcpu_get_count(HF_VM_ID_OFFSET + 1), 0);
}

/**
 * Confirm an error is returned when getting the vCPU count for a reserved ID.
 */
TEST(hf_vcpu_get_count, reserved_vm_id)
{
	spci_vm_id_t id;

	for (id = 0; id < HF_VM_ID_OFFSET; ++id) {
		EXPECT_EQ(hf_vcpu_get_count(id), 0);
	}
}

/**
 * Confirm an error is returned when getting the vCPU count of a VM with an ID
 * that is likely to be far outside the resource limit.
 */
TEST(hf_vcpu_get_count, large_invalid_vm_id)
{
	EXPECT_EQ(hf_vcpu_get_count(0xffff), 0);
}

/**
 * Confirm it is an error when running a vCPU from the primary VM.
 */
TEST(spci_run, cannot_run_primary)
{
	struct spci_value res = spci_run(HF_PRIMARY_VM_ID, 0);
	EXPECT_SPCI_ERROR(res, SPCI_INVALID_PARAMETERS);
}

/**
 * Confirm it is an error when running a vCPU from a non-existent secondary VM.
 */
TEST(spci_run, cannot_run_absent_secondary)
{
	struct spci_value res = spci_run(1, 0);
	EXPECT_SPCI_ERROR(res, SPCI_INVALID_PARAMETERS);
}

/**
 * Yielding from the primary is a noop.
 */
TEST(spci_yield, yield_is_noop_for_primary)
{
	EXPECT_EQ(spci_yield().func, SPCI_SUCCESS_32);
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

/**
 * Confirm a new CPU can be started to execute in parallel.
 */
TEST(cpus, start)
{
	struct spinlock lock = SPINLOCK_INIT;
	alignas(4096) static uint8_t other_stack[4096];

	/* Start secondary while holding lock. */
	sl_lock(&lock);
	EXPECT_EQ(hftest_cpu_start(hftest_get_cpu_id(1), other_stack,
				   sizeof(other_stack), vm_cpu_entry,
				   (uintptr_t)&lock),
		  true);

	/* Wait for CPU to release the lock. */
	sl_lock(&lock);
}

/**
 * Releases the lock passed in and then stops the CPU.
 */
static void vm_cpu_entry_stop(uintptr_t arg)
{
	struct spinlock *lock = (struct spinlock *)arg;

	dlog("Second CPU started.\n");
	sl_unlock(lock);

	dlog("Second CPU stopping.\n");
	arch_cpu_stop();

	FAIL("arch_cpu_stop() returned.");
}

/**
 * Confirm a secondary CPU can be stopped again.
 */
TEST(cpus, stop)
{
	struct spinlock lock = SPINLOCK_INIT;
	alignas(4096) static uint8_t other_stack[4096];

	/* Start secondary while holding lock. */
	sl_lock(&lock);
	dlog("Starting second CPU.\n");
	EXPECT_EQ(hftest_cpu_start(hftest_get_cpu_id(1), other_stack,
				   sizeof(other_stack), vm_cpu_entry_stop,
				   (uintptr_t)&lock),
		  true);

	/* Wait for CPU to release the lock after starting. */
	sl_lock(&lock);

	dlog("Waiting for second CPU to stop.\n");
	/* Wait a while for CPU to stop. */
	while (arch_cpu_status(hftest_get_cpu_id(1)) != POWER_STATUS_OFF) {
	}
	dlog("Second CPU stopped.\n");

	dlog("Starting second CPU again.\n");
	EXPECT_EQ(hftest_cpu_start(hftest_get_cpu_id(1), other_stack,
				   sizeof(other_stack), vm_cpu_entry_stop,
				   (uintptr_t)&lock),
		  true);

	/* Wait for CPU to release the lock after starting. */
	sl_lock(&lock);

	dlog("Waiting for second CPU to stop.\n");
	/* Wait a while for CPU to stop. */
	while (arch_cpu_status(hftest_get_cpu_id(1)) != POWER_STATUS_OFF) {
	}
	dlog("Second CPU stopped.\n");
}

/** Ensures that the Hafnium SPCI version is reported as expected. */
TEST(spci, spci_version)
{
	const int32_t major_revision = 0;
	const int32_t major_revision_offset = 16;
	const int32_t minor_revision = 9;
	const int32_t current_version =
		(major_revision << major_revision_offset) | minor_revision;

	struct spci_value ret = spci_version();
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);
	EXPECT_EQ(ret.arg2, current_version);
}

/** Ensures that SPCI_FEATURES is reporting the expected interfaces. */
TEST(spci, spci_features)
{
	struct spci_value ret;

	ret = spci_features(SPCI_ERROR_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_SUCCESS_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_VERSION_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_FEATURES_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_ID_GET_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_YIELD_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_MSG_SEND_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_MSG_POLL_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_MSG_WAIT_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);

	ret = spci_features(SPCI_YIELD_32);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);
}

/**
 * Ensures that SPCI_FEATURES returns not supported for a bogus FID or
 * currently non-implemented interfaces.
 */
TEST(spci, spci_features_not_supported)
{
	struct spci_value ret;

	ret = spci_features(0);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(0x84000000);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_INTERRUPT_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_RX_RELEASE_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_RXTX_MAP_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_RXTX_UNMAP_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_PARTITION_INFO_GET_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_RUN_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_MSG_SEND_DIRECT_RESP_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_MSG_SEND_DIRECT_REQ_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_MSG_SEND_DIRECT_REQ_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);

	ret = spci_features(SPCI_MSG_SEND_DIRECT_RESP_32);
	EXPECT_SPCI_ERROR(ret, SPCI_NOT_SUPPORTED);
}

/**
 * Test that floating-point operations work in the primary VM.
 */
TEST(fp, fp)
{
	/*
	 * Get some numbers that the compiler can't tell are constants, so it
	 * can't optimise them away.
	 */
	double a = hf_vm_get_count();
	double b = hf_vcpu_get_count(HF_PRIMARY_VM_ID);
	double result = a * b;
	dlog("VM count: %d\n", hf_vm_get_count());
	dlog("vCPU count: %d\n", hf_vcpu_get_count(HF_PRIMARY_VM_ID));
	dlog("result: %d\n", (int)result);
	EXPECT_TRUE(a == 1.0);
	EXPECT_TRUE(b == 8.0);
	EXPECT_TRUE(result == 8.0);
}
