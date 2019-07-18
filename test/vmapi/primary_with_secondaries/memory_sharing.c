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

#include <stdint.h>

#include "hf/mm.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"
#include "util.h"

alignas(PAGE_SIZE) static uint8_t page[PAGE_SIZE];

/**
 * Tries sharing memory in different modes with different VMs and asserts that
 * it will fail.
 */
void check_cannot_share_memory(void *ptr, size_t size)
{
	uint32_t vms[] = {SERVICE_VM0, SERVICE_VM1};
	enum hf_share modes[] = {HF_MEMORY_GIVE, HF_MEMORY_LEND,
				 HF_MEMORY_SHARE};
	int i;
	int j;

	for (i = 0; i < ARRAY_SIZE(vms); ++i) {
		for (j = 0; j < ARRAY_SIZE(modes); ++j) {
			ASSERT_EQ(hf_share_memory(vms[i], (hf_ipaddr_t)ptr,
						  size, modes[j]),
				  -1);
		}
	}
}

/**
 * Tries sharing memory in available modes with different VMs and asserts that
 * it will fail.
 */
static void spci_check_cannot_share_memory(
	struct mailbox_buffers mb,
	struct spci_memory_region_constituent constituents[], int num_elements)
{
	uint32_t vms[] = {HF_PRIMARY_VM_ID, SERVICE_VM0, SERVICE_VM1};
	void (*modes[])(struct spci_message *, spci_vm_id_t, spci_vm_id_t,
			struct spci_memory_region_constituent *, uint32_t,
			uint32_t) = {spci_memory_donate};
	int i;
	int j;

	for (j = 0; j < ARRAY_SIZE(modes); ++j) {
		for (i = 0; i < ARRAY_SIZE(vms); ++i) {
			modes[j](mb.send, vms[i], HF_PRIMARY_VM_ID,
				 constituents, num_elements, 0);
			EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
		}
	}
}

/**
 * After memory has been shared concurrently, it can't be shared again.
 */
TEST(memory_sharing, cannot_share_concurrent_memory_twice)
{
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_SHARE),
		  0);
	check_cannot_share_memory(page, PAGE_SIZE);
}

/**
 * After memory has been given away, it can't be shared again.
 */
TEST(memory_sharing, cannot_share_given_memory_twice)
{
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_GIVE),
		  0);
	check_cannot_share_memory(page, PAGE_SIZE);
}

/**
 * After memory has been lent, it can't be shared again.
 */
TEST(memory_sharing, cannot_share_lent_memory_twice)
{
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_LEND),
		  0);
	check_cannot_share_memory(page, PAGE_SIZE);
}

/**
 * Sharing memory concurrently gives both VMs access to the memory so it can be
 * used for communication.
 */
TEST(memory_sharing, concurrent)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "memory_increment", mb.send);

	memset_s(ptr, sizeof(page), 'a', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_SHARE),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, &ptr, sizeof(ptr));
	spci_message_init(mb.send, sizeof(ptr), SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);

	for (int i = 0; i < PAGE_SIZE; ++i) {
		page[i] = i;
	}

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	for (int i = 0; i < PAGE_SIZE; ++i) {
		uint8_t value = i + 1;

		EXPECT_EQ(page[i], value);
	}
}

/**
 * Memory shared concurrently can be returned to the owner.
 */
TEST(memory_sharing, share_concurrently_and_get_back)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "memory_return", mb.send);

	/* Dirty the memory before sharing it. */
	memset_s(ptr, sizeof(page), 'b', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_SHARE),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, &ptr, sizeof(ptr));
	spci_message_init(mb.send, sizeof(ptr), SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Let the memory be returned. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}

	/* Observe the service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * SPCI Memory given away can be given back.
 * Employing SPCI donate architected messages.
 */
TEST(memory_sharing, spci_give_and_get_back)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "spci_memory_return", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', PAGE_SIZE);

	/* Can only donate single constituent memory region. */
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID, constituents,
			   1, 0);

	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);

	/* Let the memory be returned. */
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Ensure that the secondary VM accessed the region. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'c');
	}

	/* Observe the service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * Memory given away can be given back.
 */
TEST(memory_sharing, give_and_get_back)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "memory_return", mb.send);

	/* Dirty the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_GIVE),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, &ptr, sizeof(ptr));
	spci_message_init(mb.send, sizeof(ptr), SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Let the memory be returned. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}

	/* Observe the service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * Memory that has been lent can be returned to the owner.
 */
TEST(memory_sharing, lend_and_get_back)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "memory_return", mb.send);

	/* Dirty the memory before lending it. */
	memset_s(ptr, sizeof(page), 'c', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_LEND),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, &ptr, sizeof(ptr));
	spci_message_init(mb.send, sizeof(ptr), SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Let the memory be returned. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}

	/* Observe the service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * After memory has been returned, it is free to be shared again.
 */
TEST(memory_sharing, reshare_after_return)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "memory_return", mb.send);

	/* Share the memory initially. */
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_LEND),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, &ptr, sizeof(ptr));
	spci_message_init(mb.send, sizeof(ptr), SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Let the memory be returned. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Share the memory again after it has been returned. */
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_LEND),
		  0);

	/* Observe the service doesn't fault when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);
}

/**
 * After memory has been returned, it is free to be shared with another VM.
 */
TEST(memory_sharing, share_elsewhere_after_return)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "memory_return", mb.send);

	/* Share the memory initially. */
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_LEND),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, &ptr, sizeof(ptr));
	spci_message_init(mb.send, sizeof(ptr), SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Let the memory be returned. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Share the memory with a differnt VM after it has been returned. */
	ASSERT_EQ(hf_share_memory(SERVICE_VM1, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_LEND),
		  0);

	/* Observe the service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * After memory has been given, it is no longer accessible by the sharing VM.
 */
TEST(memory_sharing, give_memory_and_lose_access)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr;

	SERVICE_SELECT(SERVICE_VM0, "give_memory_and_fault", mb.send);

	/* Have the memory be given. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Check the memory was cleared. */
	ptr = *(uint8_t **)mb.recv->payload;
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}

	/* Observe the service fault when it tries to access it. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * After memory has been lent, it is no longer accessible by the sharing VM.
 */
TEST(memory_sharing, lend_memory_and_lose_access)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr;

	SERVICE_SELECT(SERVICE_VM0, "lend_memory_and_fault", mb.send);

	/* Have the memory be lent. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Check the memory was cleared. */
	ptr = *(uint8_t **)mb.recv->payload;
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}

	/* Observe the service fault when it tries to access it. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * SPCI: Verify past the upper bound of the donated region cannot be accessed.
 */
TEST(memory_sharing, spci_donate_check_upper_bounds)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "spci_donate_check_upper_bound", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID, constituents,
			   1, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Observe the service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * SPCI: Verify past the lower bound of the donated region cannot be accessed.
 */
TEST(memory_sharing, spci_donate_check_lower_bounds)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "spci_donate_check_lower_bound", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID, constituents,
			   1, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Observe the service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * SPCI: After memory has been returned, it is free to be shared with another
 * VM.
 */
TEST(memory_sharing, spci_donate_elsewhere_after_return)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "spci_memory_return", mb.send);
	SERVICE_SELECT(SERVICE_VM1, "spci_memory_return", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID, constituents,
			   1, 0);

	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);

	/* Let the memory be returned. */
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Share the memory with another VM. */
	spci_memory_donate(mb.send, SERVICE_VM1, HF_PRIMARY_VM_ID, constituents,
			   1, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Observe the original service faulting when accessing the memory. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}

/**
 * SPCI: Check if memory can be donated between secondary VMs.
 * Ensure that the memory can no longer be accessed by the first VM.
 */
TEST(memory_sharing, spci_donate_vms)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "spci_donate_secondary_and_fault", mb.send);
	SERVICE_SELECT(SERVICE_VM1, "spci_memory_receive", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	/* Set up VM1 to wait for message. */
	run_res = hf_vcpu_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);

	/* Donate memory. */
	spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID, constituents,
			   1, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Let the memory be sent from VM0 to VM1. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Receive memory in VM1. */
	run_res = hf_vcpu_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);

	/* Try to access memory in VM0 and fail. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);

	/* Ensure that memory in VM1 remains the same. */
	run_res = hf_vcpu_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
}

/**
 * SPCI: Check that memory is unable to be donated to multiple parties.
 */
TEST(memory_sharing, spci_donate_twice)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "spci_donate_twice", mb.send);
	SERVICE_SELECT(SERVICE_VM1, "spci_memory_receive", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	/* Donate memory to VM0. */
	spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID, constituents,
			   1, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Let the memory be received. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);

	/* Fail to share memory again with either VM0 or VM1. */
	spci_check_cannot_share_memory(mb, constituents, 1);

	/* Let the memory be sent from VM0 to PRIMARY (returned). */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Check we have access again. */
	ptr[0] = 'f';

	/* Try and fail to donate memory from VM0 to VM1. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
}

/**
 * SPCI: Check cannot donate to self.
 */
TEST(memory_sharing, spci_donate_to_self)
{
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', PAGE_SIZE);
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	spci_memory_donate(mb.send, HF_PRIMARY_VM_ID, HF_PRIMARY_VM_ID,
			   constituents, 1, 0);

	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
}

/**
 * SPCI: Check cannot donate from alternative VM.
 */
TEST(memory_sharing, spci_donate_invalid_source)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "spci_donate_invalid_source", mb.send);
	SERVICE_SELECT(SERVICE_VM1, "spci_memory_receive", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(page), 'b', PAGE_SIZE);
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)page, .page_count = 1},
	};

	/* Try invalid configurations. */
	spci_memory_donate(mb.send, HF_PRIMARY_VM_ID, SERVICE_VM0, constituents,
			   1, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);

	spci_memory_donate(mb.send, SERVICE_VM0, SERVICE_VM0, constituents, 1,
			   0);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);

	spci_memory_donate(mb.send, SERVICE_VM0, SERVICE_VM1, constituents, 1,
			   0);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);

	/* Successfully donate to VM0. */
	spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID, constituents,
			   1, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Receive and return memory from VM0. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Use VM0 to fail to donate memory from the primary to VM1. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
}

/**
 * SPCI: Check that unaligned addresses can not be donated.
 */
TEST(memory_sharing, spci_give_and_get_back_unaligned)
{
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "spci_memory_return", mb.send);

	for (int i = 1; i < PAGE_SIZE; i++) {
		struct spci_memory_region_constituent constituents[] = {
			{.address = (uint64_t)page + i, .page_count = 1},
		};
		spci_memory_donate(mb.send, SERVICE_VM0, HF_PRIMARY_VM_ID,
				   constituents, 1, 0);
		EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
	}
}
