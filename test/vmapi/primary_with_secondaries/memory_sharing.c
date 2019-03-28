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

#include "hf/arch/std.h"

#include "hf/mm.h"

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

	memset(ptr, 'a', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_SHARE),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy(mb.send, &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(ptr), false), 0);

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
	memset(ptr, 'b', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_SHARE),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy(mb.send, &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(ptr), false), 0);

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
 * Memory given away can be given back.
 */
TEST(memory_sharing, give_and_get_back)
{
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = page;

	SERVICE_SELECT(SERVICE_VM0, "memory_return", mb.send);

	/* Dirty the memory before giving it. */
	memset(ptr, 'b', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_GIVE),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy(mb.send, &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(ptr), false), 0);

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
	memset(ptr, 'c', PAGE_SIZE);
	ASSERT_EQ(hf_share_memory(SERVICE_VM0, (hf_ipaddr_t)&page, PAGE_SIZE,
				  HF_MEMORY_LEND),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy(mb.send, &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(ptr), false), 0);

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
	memcpy(mb.send, &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(ptr), false), 0);

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
	memcpy(mb.send, &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(ptr), false), 0);

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
	memcpy(&ptr, mb.recv, sizeof(ptr));
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
	memcpy(&ptr, mb.recv, sizeof(ptr));
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}

	/* Observe the service fault when it tries to access it. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_ABORTED);
}
