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
#include <stdint.h>

#include "hf/mm.h"
#include "hf/static_assert.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "primary_with_secondary.h"
#include "test/hftest.h"
#include "test/vmapi/spci.h"

static alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
static alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];
static_assert(sizeof(send_page) == PAGE_SIZE, "Send page is not a page.");
static_assert(sizeof(recv_page) == PAGE_SIZE, "Recv page is not a page.");

static hf_ipaddr_t send_page_addr = (hf_ipaddr_t)send_page;
static hf_ipaddr_t recv_page_addr = (hf_ipaddr_t)recv_page;

/**
 * Confirms the primary VM has the primary ID.
 */
TEST(hf_vm_get_id, primary_has_primary_id)
{
	EXPECT_EQ(hf_vm_get_id(), HF_PRIMARY_VM_ID);
}

/**
 * Confirm there are 3 secondary VMs as well as this primary VM.
 */
TEST(hf_vm_get_count, three_secondary_vms)
{
	EXPECT_EQ(hf_vm_get_count(), 4);
}

/**
 * Confirm that secondary VM has 1 vCPU.
 */
TEST(hf_vcpu_get_count, secondary_has_one_vcpu)
{
	EXPECT_EQ(hf_vcpu_get_count(SERVICE_VM1), 1);
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
 * Confirm it is an error to query how many vCPUs are assigned to a nonexistent
 * secondary VM.
 */
TEST(hf_vcpu_get_count, large_invalid_vm_id)
{
	EXPECT_EQ(hf_vcpu_get_count(0xffff), 0);
}

/**
 * The primary can't be run by the hypervisor.
 */
TEST(spci_run, cannot_run_primary)
{
	struct spci_value res = spci_run(HF_PRIMARY_VM_ID, 0);
	EXPECT_SPCI_ERROR(res, SPCI_INVALID_PARAMETERS);
}

/**
 * Can only run a VM that exists.
 */
TEST(spci_run, cannot_run_absent_secondary)
{
	struct spci_value res = spci_run(1234, 0);
	EXPECT_SPCI_ERROR(res, SPCI_INVALID_PARAMETERS);
}

/**
 * Can only run a vCPU that exists.
 */
TEST(spci_run, cannot_run_absent_vcpu)
{
	struct spci_value res = spci_run(SERVICE_VM1, 1234);
	EXPECT_SPCI_ERROR(res, SPCI_INVALID_PARAMETERS);
}

/**
 * The configured send/receive addresses can't be device memory.
 */
TEST(spci_rxtx_map, fails_with_device_memory)
{
	EXPECT_SPCI_ERROR(spci_rxtx_map(PAGE_SIZE, PAGE_SIZE * 2), SPCI_DENIED);
}

/**
 * The configured send/receive addresses can't be unaligned.
 */
TEST(spci_rxtx_map, fails_with_unaligned_pointer)
{
	uint8_t maybe_aligned[2];
	hf_ipaddr_t unaligned_addr = (hf_ipaddr_t)&maybe_aligned[1];
	hf_ipaddr_t aligned_addr = (hf_ipaddr_t)send_page;

	/* Check that the address is unaligned. */
	ASSERT_EQ(unaligned_addr & 1, 1);

	EXPECT_SPCI_ERROR(spci_rxtx_map(aligned_addr, unaligned_addr),
			  SPCI_INVALID_PARAMETERS);
	EXPECT_SPCI_ERROR(spci_rxtx_map(unaligned_addr, aligned_addr),
			  SPCI_INVALID_PARAMETERS);
	EXPECT_SPCI_ERROR(spci_rxtx_map(unaligned_addr, unaligned_addr),
			  SPCI_INVALID_PARAMETERS);
}

/**
 * The configured send/receive addresses can't be the same page.
 */
TEST(spci_rxtx_map, fails_with_same_page)
{
	EXPECT_SPCI_ERROR(spci_rxtx_map(send_page_addr, send_page_addr),
			  SPCI_INVALID_PARAMETERS);
	EXPECT_SPCI_ERROR(spci_rxtx_map(recv_page_addr, recv_page_addr),
			  SPCI_INVALID_PARAMETERS);
}

/**
 * The configuration of the send/receive addresses can only happen once.
 */
TEST(spci_rxtx_map, fails_if_already_succeeded)
{
	EXPECT_EQ(spci_rxtx_map(send_page_addr, recv_page_addr).func,
		  SPCI_SUCCESS_32);
	EXPECT_SPCI_ERROR(spci_rxtx_map(send_page_addr, recv_page_addr),
			  SPCI_DENIED);
}

/**
 * The configuration of the send/receive address is successful with valid
 * arguments.
 */
TEST(spci_rxtx_map, succeeds)
{
	EXPECT_EQ(spci_rxtx_map(send_page_addr, recv_page_addr).func,
		  SPCI_SUCCESS_32);
}

/**
 * The primary receives messages from spci_run().
 */
TEST(hf_mailbox_receive, cannot_receive_from_primary_blocking)
{
	struct spci_value res = spci_msg_wait();
	EXPECT_NE(res.func, SPCI_SUCCESS_32);
}

/**
 * The primary receives messages from spci_run().
 */
TEST(hf_mailbox_receive, cannot_receive_from_primary_non_blocking)
{
	struct spci_value res = spci_msg_poll();
	EXPECT_NE(res.func, SPCI_SUCCESS_32);
}
