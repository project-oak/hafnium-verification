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

#include "primary_with_secondary.h"
#include "test/hftest.h"
#include "test/vmapi/exception_handler.h"
#include "test/vmapi/spci.h"

alignas(PAGE_SIZE) static uint8_t pages[4 * PAGE_SIZE];

/**
 * Helper function to test sending memory in the different configurations.
 */
static void check_cannot_send_memory(
	struct mailbox_buffers mb,
	struct spci_value (*send_function)(uint32_t, uint32_t, uint32_t),
	struct spci_memory_region_constituent constituents[],
	int constituent_count, int32_t avoid_vm)

{
	enum spci_memory_access access[] = {SPCI_MEMORY_RO_NX, SPCI_MEMORY_RO_X,
					    SPCI_MEMORY_RW_NX,
					    SPCI_MEMORY_RW_X};
	enum spci_memory_cacheability cacheability[] = {
		SPCI_MEMORY_CACHE_NON_CACHEABLE,
		SPCI_MEMORY_CACHE_WRITE_THROUGH, SPCI_MEMORY_CACHE_WRITE_BACK};
	enum spci_memory_cacheability device[] = {
		SPCI_MEMORY_DEV_NGNRNE, SPCI_MEMORY_DEV_NGNRE,
		SPCI_MEMORY_DEV_NGRE, SPCI_MEMORY_DEV_GRE};
	enum spci_memory_shareability shareability[] = {
		SPCI_MEMORY_SHARE_NON_SHAREABLE, SPCI_MEMORY_RESERVED,
		SPCI_MEMORY_OUTER_SHAREABLE, SPCI_MEMORY_INNER_SHAREABLE};
	uint32_t vms[] = {HF_PRIMARY_VM_ID, SERVICE_VM1, SERVICE_VM2};

	size_t i = 0;
	size_t j = 0;
	size_t k = 0;
	size_t l = 0;

	for (i = 0; i < ARRAY_SIZE(vms); ++i) {
		/* Optionally skip one VM as the send would succeed. */
		if (vms[i] == avoid_vm) {
			continue;
		}
		for (j = 0; j < ARRAY_SIZE(access); ++j) {
			for (k = 0; k < ARRAY_SIZE(shareability); ++k) {
				for (l = 0; l < ARRAY_SIZE(cacheability); ++l) {
					uint32_t msg_size =
						spci_memory_region_init(
							mb.send,
							HF_PRIMARY_VM_ID,
							vms[i], constituents,
							constituent_count, 0, 0,
							access[j],
							SPCI_MEMORY_NORMAL_MEM,
							cacheability[l],
							shareability[k]);
					EXPECT_SPCI_ERROR(
						send_function(msg_size,
							      msg_size, 0),
						SPCI_INVALID_PARAMETERS);
				}
				for (l = 0; l < ARRAY_SIZE(device); ++l) {
					uint32_t msg_size =
						spci_memory_region_init(
							mb.send,
							HF_PRIMARY_VM_ID,
							vms[i], constituents,
							constituent_count, 0, 0,
							access[j],
							SPCI_MEMORY_DEVICE_MEM,
							device[l],
							shareability[k]);
					EXPECT_SPCI_ERROR(
						send_function(msg_size,
							      msg_size, 0),
						SPCI_INVALID_PARAMETERS);
				}
			}
		}
	}
}

/**
 * Helper function to test lending memory in the different configurations.
 */
static void check_cannot_lend_memory(
	struct mailbox_buffers mb,
	struct spci_memory_region_constituent constituents[],
	int constituent_count, int32_t avoid_vm)

{
	check_cannot_send_memory(mb, spci_mem_lend, constituents,
				 constituent_count, avoid_vm);
}

/**
 * Helper function to test sharing memory in the different configurations.
 */
static void check_cannot_share_memory(
	struct mailbox_buffers mb,
	struct spci_memory_region_constituent constituents[],
	int constituent_count, int32_t avoid_vm)

{
	check_cannot_send_memory(mb, spci_mem_share, constituents,
				 constituent_count, avoid_vm);
}

/**
 * Tries donating memory in available modes with different VMs and asserts that
 * it will fail to all except the supplied VM ID as this would succeed if it
 * is the only borrower.
 */
static void check_cannot_donate_memory(
	struct mailbox_buffers mb,
	struct spci_memory_region_constituent constituents[],
	int constituent_count, int32_t avoid_vm)
{
	uint32_t vms[] = {HF_PRIMARY_VM_ID, SERVICE_VM1, SERVICE_VM2};

	size_t i;
	for (i = 0; i < ARRAY_SIZE(vms); ++i) {
		uint32_t msg_size;
		/* Optionally skip one VM as the donate would succeed. */
		if (vms[i] == avoid_vm) {
			continue;
		}
		msg_size = spci_memory_region_init(
			mb.send, HF_PRIMARY_VM_ID, vms[i], constituents,
			constituent_count, 0, 0, SPCI_MEMORY_RW_X,
			SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
			SPCI_MEMORY_OUTER_SHAREABLE);
		EXPECT_SPCI_ERROR(spci_mem_donate(msg_size, msg_size, 0),
				  SPCI_INVALID_PARAMETERS);
	}
}

/**
 * Tries relinquishing memory with different VMs and asserts that
 * it will fail.
 */
static void check_cannot_relinquish_memory(
	struct mailbox_buffers mb,
	struct spci_memory_region_constituent constituents[],
	int constituent_count)
{
	uint32_t vms[] = {HF_PRIMARY_VM_ID, SERVICE_VM1, SERVICE_VM2};

	size_t i;
	size_t j;
	for (i = 0; i < ARRAY_SIZE(vms); ++i) {
		for (j = 0; j < ARRAY_SIZE(vms); ++j) {
			uint32_t msg_size = spci_memory_region_init(
				mb.send, vms[j], vms[i], constituents,
				constituent_count, 0, 0, SPCI_MEMORY_RW_X,
				SPCI_MEMORY_NORMAL_MEM,
				SPCI_MEMORY_CACHE_WRITE_BACK,
				SPCI_MEMORY_OUTER_SHAREABLE);
			EXPECT_SPCI_ERROR(
				hf_spci_mem_relinquish(msg_size, msg_size, 0),
				SPCI_INVALID_PARAMETERS);
		}
	}
}

TEAR_DOWN(memory_sharing)
{
	EXPECT_SPCI_ERROR(spci_rx_release(), SPCI_DENIED);
}

/**
 * Sharing memory concurrently gives both VMs access to the memory so it can be
 * used for communication.
 */
TEST(memory_sharing, concurrent)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	SERVICE_SELECT(SERVICE_VM1, "memory_increment", mb.send);

	memset_s(ptr, sizeof(pages), 'a', PAGE_SIZE);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, SPCI_MEMORY_REGION_FLAG_CLEAR,
		SPCI_MEMORY_RW_X, SPCI_MEMORY_NORMAL_MEM,
		SPCI_MEMORY_CACHE_WRITE_BACK, SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	for (int i = 0; i < PAGE_SIZE; ++i) {
		pages[i] = i;
	}

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_SEND_32);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	for (int i = 0; i < PAGE_SIZE; ++i) {
		uint8_t value = i + 1;

		EXPECT_EQ(pages[i], value);
	}
}

/**
 * Memory shared concurrently can be returned to the owner.
 */
TEST(memory_sharing, share_concurrently_and_get_back)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish", mb.send);

	/* Dirty the memory before sharing it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be returned. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'c');
	}
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Device address space cannot be shared, only normal memory.
 */
TEST(memory_sharing, cannot_share_device_memory)
{
	struct mailbox_buffers mb = set_up_mailbox();
	struct spci_memory_region_constituent constituents[] = {
		{.address = PAGE_SIZE, .page_count = 1},
	};

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_return", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_return", mb.send);

	check_cannot_lend_memory(mb, constituents, ARRAY_SIZE(constituents),
				 -1);
	check_cannot_share_memory(mb, constituents, ARRAY_SIZE(constituents),
				  -1);
	check_cannot_donate_memory(mb, constituents, ARRAY_SIZE(constituents),
				   -1);
}

/**
 * Check that memory can be lent and is accessible by both parties.
 */
TEST(memory_sharing, lend_relinquish)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
		{.address = (uint64_t)pages + PAGE_SIZE, .page_count = 2},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);
	run_res = spci_run(SERVICE_VM1, 0);

	/* Let the memory be returned. */
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Ensure that the secondary VM accessed the region. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'c');
	}

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Check that memory that is donated can't be relinquished.
 */
TEST(memory_sharing, donate_relinquish)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_donate_relinquish", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
		{.address = (uint64_t)pages + PAGE_SIZE, .page_count = 2},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/*
	 * Let the service access the memory, and try and fail to relinquish it.
	 */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Memory given away can be given back.
 */
TEST(memory_sharing, give_and_get_back)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_return", mb.send);

	/* Dirty the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be returned. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MEM_DONATE_32);
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'c');
	}
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Memory that has been lent can be returned to the owner.
 */
TEST(memory_sharing, lend_and_get_back)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish", mb.send);

	/* Dirty the memory before lending it. */
	memset_s(ptr, sizeof(pages), 'c', PAGE_SIZE);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be returned. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'd');
	}
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * After memory has been returned, it is free to be shared again.
 */
TEST(memory_sharing, reshare_after_return)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint32_t msg_size;
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish", mb.send);

	/* Share the memory initially. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be returned. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Share the memory again after it has been returned. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Observe the service doesn't fault when accessing the memory. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);
}

/**
 * After memory has been returned, it is free to be shared with another VM.
 */
TEST(memory_sharing, share_elsewhere_after_return)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint32_t msg_size;
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_lend_relinquish", mb.send);

	/* Share the memory initially. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be returned. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Share the memory with a different VM after it has been returned. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * After memory has been given, it is no longer accessible by the sharing VM.
 */
TEST(memory_sharing, give_memory_and_lose_access)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	struct spci_memory_region *memory_region;
	struct spci_memory_region_constituent *constituents;
	uint8_t *ptr;

	SERVICE_SELECT(SERVICE_VM1, "give_memory_and_fault", mb.send);

	/* Have the memory be given. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MEM_DONATE_32);

	/* Check the memory was cleared. */
	memory_region = (struct spci_memory_region *)mb.recv;
	constituents = spci_memory_region_get_constituents(memory_region);
	ptr = (uint8_t *)constituents[0].address;
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * After memory has been lent, it is no longer accessible by the sharing VM.
 */
TEST(memory_sharing, lend_memory_and_lose_access)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	struct spci_memory_region *memory_region;
	struct spci_memory_region_constituent *constituents;
	uint8_t *ptr;

	SERVICE_SELECT(SERVICE_VM1, "lend_memory_and_fault", mb.send);

	/* Have the memory be lent. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MEM_LEND_32);

	/* Check the memory was cleared. */
	memory_region = (struct spci_memory_region *)mb.recv;
	constituents = spci_memory_region_get_constituents(memory_region);
	ptr = (uint8_t *)constituents[0].address;
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 0);
	}
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Verify past the upper bound of the donated region cannot be accessed.
 */
TEST(memory_sharing, donate_check_upper_bounds)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_donate_check_upper_bound", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', 4 * PAGE_SIZE);

	/* Specify non-contiguous memory regions. */
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
		{.address = (uint64_t)pages + PAGE_SIZE * 2, .page_count = 1},
	};

	/*
	 * Specify that we want to test the first constituent of the donated
	 * memory region. This is utilised by the test service.
	 */
	pages[0] = 0;

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);

	/* Use different memory regions for verifying the second constituent. */
	constituents[0].address = (uint64_t)pages + PAGE_SIZE * 1;
	constituents[1].address = (uint64_t)pages + PAGE_SIZE * 3;

	/*
	 * Specify that we now want to test the second constituent of the
	 * donated memory region.
	 */
	pages[PAGE_SIZE] = 1;

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Verify past the lower bound of the donated region cannot be accessed.
 */
TEST(memory_sharing, donate_check_lower_bounds)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_donate_check_lower_bound", mb.send);

	/* Initialise the memory before donating it. */
	memset_s(ptr, sizeof(pages), 'b', 4 * PAGE_SIZE);

	/* Specify non-contiguous memory regions. */
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
		{.address = (uint64_t)pages + PAGE_SIZE * 2, .page_count = 1},
	};

	/*
	 * Specify that we want to test the first constituent of the donated
	 * memory region. This is utilised by the test service.
	 */
	pages[0] = 0;

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);

	/* Use different memory regions for verifying the second constituent. */
	constituents[0].address = (uint64_t)pages + PAGE_SIZE * 1;
	constituents[1].address = (uint64_t)pages + PAGE_SIZE * 3;

	/*
	 * Specify that we now want to test the second constituent of the
	 * donated memory region.
	 */
	pages[PAGE_SIZE] = 1;

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	/*
	 * NOTE: This generates two exceptions, one for the page fault, and one
	 * for accessing a region past the lower bound.
	 */
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  2);
}

/**
 * After memory has been returned, it is free to be shared with another
 * VM.
 */
TEST(memory_sharing, donate_elsewhere_after_return)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_return", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_return", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);
	run_res = spci_run(SERVICE_VM1, 0);

	/* Let the memory be returned. */
	EXPECT_EQ(run_res.func, SPCI_MEM_DONATE_32);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Share the memory with another VM. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Check if memory can be donated between secondary VMs.
 * Ensure that the memory can no longer be accessed by the first VM.
 */
TEST(memory_sharing, donate_vms)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_donate_secondary_and_fault", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_receive", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	/* Set up VM2 to wait for message. */
	run_res = spci_run(SERVICE_VM2, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_WAIT_32);

	/* Donate memory. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be sent from VM1 to VM2. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_SEND_32);
	EXPECT_EQ(spci_msg_send_receiver(run_res), SERVICE_VM2);

	/* Receive memory in VM2. */
	run_res = spci_run(SERVICE_VM2, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Try to access memory in VM1. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);

	/* Ensure that memory in VM2 remains the same. */
	run_res = spci_run(SERVICE_VM2, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Check that memory is unable to be donated to multiple parties.
 */
TEST(memory_sharing, donate_twice)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_donate_twice", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_receive", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', 1 * PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	/* Donate memory to VM1. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be received. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Fail to share memory again with any VM. */
	check_cannot_share_memory(mb, constituents, ARRAY_SIZE(constituents),
				  -1);
	check_cannot_lend_memory(mb, constituents, ARRAY_SIZE(constituents),
				 -1);
	check_cannot_donate_memory(mb, constituents, ARRAY_SIZE(constituents),
				   -1);
	/* Fail to relinquish memory from any VM. */
	check_cannot_relinquish_memory(mb, constituents,
				       ARRAY_SIZE(constituents));

	/* Let the memory be sent from VM1 to PRIMARY (returned). */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MEM_DONATE_32);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Check we have access again. */
	ptr[0] = 'f';

	/* Try and fail to donate memory from VM1 to VM2. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Check cannot donate to self.
 */
TEST(memory_sharing, donate_to_self)
{
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, HF_PRIMARY_VM_ID, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_SPCI_ERROR(spci_mem_donate(msg_size, msg_size, 0),
			  SPCI_INVALID_PARAMETERS);
}

/**
 * Check cannot lend to self.
 */
TEST(memory_sharing, lend_to_self)
{
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, HF_PRIMARY_VM_ID, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_SPCI_ERROR(spci_mem_lend(msg_size, msg_size, 0),
			  SPCI_INVALID_PARAMETERS);
}

/**
 * Check cannot share to self.
 */
TEST(memory_sharing, share_to_self)
{
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, HF_PRIMARY_VM_ID, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_SPCI_ERROR(spci_mem_share(msg_size, msg_size, 0),
			  SPCI_INVALID_PARAMETERS);
}

/**
 * Check cannot donate from alternative VM.
 */
TEST(memory_sharing, donate_invalid_source)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_donate_invalid_source", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_receive", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	/* Try invalid configurations. */
	msg_size = spci_memory_region_init(
		mb.send, SERVICE_VM1, HF_PRIMARY_VM_ID, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_SPCI_ERROR(spci_mem_donate(msg_size, msg_size, 0),
			  SPCI_INVALID_PARAMETERS);

	msg_size = spci_memory_region_init(
		mb.send, SERVICE_VM1, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_SPCI_ERROR(spci_mem_donate(msg_size, msg_size, 0),
			  SPCI_INVALID_PARAMETERS);

	msg_size = spci_memory_region_init(
		mb.send, SERVICE_VM2, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_SPCI_ERROR(spci_mem_donate(msg_size, msg_size, 0),
			  SPCI_INVALID_PARAMETERS);

	/* Successfully donate to VM1. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Receive and return memory from VM1. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MEM_DONATE_32);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Use VM1 to fail to donate memory from the primary to VM2. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Check that unaligned addresses can not be shared.
 */
TEST(memory_sharing, give_and_get_back_unaligned)
{
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_return", mb.send);

	/* Check for unaligned pages for either constituent. */
	for (int i = 0; i < PAGE_SIZE; i++) {
		for (int j = 0; i < PAGE_SIZE; i++) {
			/* Skip the case they're both aligned. */
			if (i == 0 && j == 0) {
				continue;
			}
			struct spci_memory_region_constituent constituents[] = {
				{.address = (uint64_t)pages + i,
				 .page_count = 1},
				{.address = (uint64_t)pages + PAGE_SIZE + j,
				 .page_count = 1},
			};
			uint32_t msg_size = spci_memory_region_init(
				mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1,
				constituents, ARRAY_SIZE(constituents), 0, 0,
				SPCI_MEMORY_RW_X, SPCI_MEMORY_NORMAL_MEM,
				SPCI_MEMORY_CACHE_WRITE_BACK,
				SPCI_MEMORY_OUTER_SHAREABLE);
			EXPECT_SPCI_ERROR(
				spci_mem_donate(msg_size, msg_size, 0),
				SPCI_INVALID_PARAMETERS);
			msg_size = spci_memory_region_init(
				mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1,
				constituents, ARRAY_SIZE(constituents), 0, 0,
				SPCI_MEMORY_RW_X, SPCI_MEMORY_NORMAL_MEM,
				SPCI_MEMORY_CACHE_WRITE_BACK,
				SPCI_MEMORY_OUTER_SHAREABLE);
			EXPECT_SPCI_ERROR(spci_mem_lend(msg_size, msg_size, 0),
					  SPCI_INVALID_PARAMETERS);
		}
	}
}

/**
 * Check cannot lend from alternative VM.
 */
TEST(memory_sharing, lend_invalid_source)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_lend_invalid_source", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	/* Check cannot swap VM IDs. */
	msg_size = spci_memory_region_init(
		mb.send, SERVICE_VM1, HF_PRIMARY_VM_ID, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_SPCI_ERROR(spci_mem_lend(msg_size, msg_size, 0),
			  SPCI_INVALID_PARAMETERS);

	/* Lend memory to VM1. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Receive and return memory from VM1. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Try to lend memory from primary in VM1. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Memory can be lent with executable permissions.
 * Check RO and RW permissions.
 */
TEST(memory_sharing, lend_relinquish_X_RW)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish_RW", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Let service write to and return memory. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Re-initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Memory can be shared with executable permissions.
 * Check RO and RW permissions.
 */
TEST(memory_sharing, share_relinquish_X_RW)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish_RW", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Ensure we still have access. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'b');
		ptr[i]++;
	}

	/* Let service write to and return memory. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Re-initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Ensure we still have access. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'b');
		ptr[i]++;
	}

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Memory can be shared without executable permissions.
 * Check RO and RW permissions.
 */
TEST(memory_sharing, share_relinquish_NX_RW)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish_RW", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_NX,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Ensure we still have access. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'b');
	}

	/* Let service write to and return memory. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Re-initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_NX,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Ensure we still have access. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ASSERT_EQ(ptr[i], 'b');
		ptr[i]++;
	}

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Exercise execution permissions for lending memory.
 */
TEST(memory_sharing, lend_relinquish_RW_X)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish_X", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 0, PAGE_SIZE);

	uint64_t *ptr2 = (uint64_t *)pages;
	/* Set memory to contain the RET instruction to attempt to execute. */
	*ptr2 = 0xD65F03C0;

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Attempt to execute from memory. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_NX,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Exercise execution permissions for lending memory without write access.
 */
TEST(memory_sharing, lend_relinquish_RO_X)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish_X", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 0, PAGE_SIZE);

	uint64_t *ptr2 = (uint64_t *)pages;
	/* Set memory to contain the RET instruction to attempt to execute. */
	*ptr2 = 0xD65F03C0;

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Attempt to execute from memory. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_MEM_RELINQUISH);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_NX,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * Memory can be lent, but then no part can be donated.
 */
TEST(memory_sharing, lend_donate)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish_RW", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_lend_relinquish_RW", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages) * 2, 'b', PAGE_SIZE * 2);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 2},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Ensure we can't donate any sub section of memory to another VM. */
	constituents[0].page_count = 1;
	for (int i = 1; i < PAGE_SIZE * 2; i++) {
		constituents[0].address = (uint64_t)pages + PAGE_SIZE;
		msg_size = spci_memory_region_init(
			mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
			ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
			SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
			SPCI_MEMORY_OUTER_SHAREABLE);
		EXPECT_SPCI_ERROR(spci_mem_donate(msg_size, msg_size, 0),
				  SPCI_INVALID_PARAMETERS);
	}

	/* Ensure we can donate to the only borrower. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);
}

/**
 * Memory can be shared, but then no part can be donated.
 */
TEST(memory_sharing, share_donate)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_relinquish_RW", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_lend_relinquish_RW", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE * 4);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 2},
		{.address = (uint64_t)pages + PAGE_SIZE * 2, .page_count = 2},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Attempt to share the same area of memory. */
	check_cannot_share_memory(mb, constituents, ARRAY_SIZE(constituents),
				  SERVICE_VM1);

	/* Ensure we can't donate any sub section of memory to another VM. */
	constituents[0].page_count = 1;
	for (int i = 1; i < PAGE_SIZE * 2; i++) {
		constituents[0].address = (uint64_t)pages + PAGE_SIZE;
		msg_size = spci_memory_region_init(
			mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
			ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
			SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
			SPCI_MEMORY_OUTER_SHAREABLE);
		EXPECT_SPCI_ERROR(spci_mem_donate(msg_size, msg_size, 0),
				  SPCI_INVALID_PARAMETERS);
	}

	/* Ensure we can donate to the only borrower. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_donate(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);
}

/**
 * Memory can be lent, but then no part can be lent again.
 */
TEST(memory_sharing, lend_twice)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_twice", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_lend_twice", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages), 'b', PAGE_SIZE * 4);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 2},
		{.address = (uint64_t)pages + PAGE_SIZE * 3, .page_count = 1},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/* Attempt to lend the same area of memory. */
	check_cannot_lend_memory(mb, constituents, ARRAY_SIZE(constituents),
				 -1);
	/* Attempt to share the same area of memory. */
	check_cannot_share_memory(mb, constituents, ARRAY_SIZE(constituents),
				  -1);
	/* Fail to donate to VM apart from VM1. */
	check_cannot_donate_memory(mb, constituents, ARRAY_SIZE(constituents),
				   SERVICE_VM1);
	/* Fail to relinquish from any VM. */
	check_cannot_relinquish_memory(mb, constituents,
				       ARRAY_SIZE(constituents));

	/* Now attempt to share only a portion of the same area of memory. */
	struct spci_memory_region_constituent constituents_subsection[] = {
		{.address = (uint64_t)pages + PAGE_SIZE * 3, .page_count = 1},
	};
	check_cannot_lend_memory(mb, constituents_subsection,
				 ARRAY_SIZE(constituents_subsection), -1);
	check_cannot_donate_memory(mb, constituents_subsection,
				   ARRAY_SIZE(constituents_subsection),
				   SERVICE_VM1);
	check_cannot_relinquish_memory(mb, constituents_subsection,
				       ARRAY_SIZE(constituents_subsection));

	/* Attempt to lend again with different permissions. */
	constituents[0].page_count = 1;
	for (int i = 0; i < 2; i++) {
		constituents[0].address = (uint64_t)pages + i * PAGE_SIZE;
		msg_size = spci_memory_region_init(
			mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
			ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_X,
			SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
			SPCI_MEMORY_OUTER_SHAREABLE);
		EXPECT_SPCI_ERROR(spci_mem_lend(msg_size, msg_size, 0),
				  SPCI_INVALID_PARAMETERS);
	}
}

/**
 * Memory can be shared, but then no part can be shared again.
 */
TEST(memory_sharing, share_twice)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_lend_twice", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_memory_lend_twice", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages) * 2, 'b', PAGE_SIZE * 2);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 2},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);

	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Let the memory be accessed. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);

	/*
	 * Attempting to share or lend the same area of memory with any VM
	 * should fail.
	 */
	check_cannot_share_memory(mb, constituents, ARRAY_SIZE(constituents),
				  -1);
	check_cannot_lend_memory(mb, constituents, ARRAY_SIZE(constituents),
				 -1);
	/* Fail to donate to VM apart from VM1. */
	check_cannot_donate_memory(mb, constituents, ARRAY_SIZE(constituents),
				   SERVICE_VM1);
	/* Fail to relinquish from any VM. */
	check_cannot_relinquish_memory(mb, constituents,
				       ARRAY_SIZE(constituents));

	/* Attempt to share again with different permissions. */
	constituents[0].page_count = 1;
	for (int i = 0; i < 2; i++) {
		constituents[0].address = (uint64_t)pages + i * PAGE_SIZE;
		msg_size = spci_memory_region_init(
			mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
			ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RO_X,
			SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
			SPCI_MEMORY_OUTER_SHAREABLE);
		EXPECT_SPCI_ERROR(spci_mem_share(msg_size, msg_size, 0),
				  SPCI_INVALID_PARAMETERS);
	}
}

/**
 * Memory can be cleared while being shared.
 */
TEST(memory_sharing, share_clear)
{
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;
	size_t i;

	SERVICE_SELECT(SERVICE_VM1, "spci_memory_return", mb.send);

	/* Initialise the memory before giving it. */
	memset_s(ptr, sizeof(pages) * 2, 'b', PAGE_SIZE * 2);

	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 2},
	};

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, SPCI_MEMORY_REGION_FLAG_CLEAR,
		SPCI_MEMORY_RO_X, SPCI_MEMORY_NORMAL_MEM,
		SPCI_MEMORY_CACHE_WRITE_BACK, SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_share(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	/* Check that it has been cleared. */
	for (i = 0; i < PAGE_SIZE * 2; ++i) {
		ASSERT_EQ(ptr[i], 0);
	};
}

/**
 * SPCI: Verify past the upper bound of the lent region cannot be accessed.
 */
TEST(memory_sharing, spci_lend_check_upper_bounds)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_lend_check_upper_bound", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_lend_check_upper_bound", mb.send);

	/* Initialise the memory before lending it. */
	memset_s(ptr, sizeof(pages), 'b', 4 * PAGE_SIZE);

	/* Specify non-contiguous memory regions. */
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
		{.address = (uint64_t)pages + PAGE_SIZE * 2, .page_count = 1},
	};

	/*
	 * Specify that we want to test the first constituent of the donated
	 * memory region. This is utilised by the test service.
	 */
	pages[0] = 0;

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);

	/* Use different memory regions for verifying the second constituent. */
	constituents[0].address = (uint64_t)pages + PAGE_SIZE * 1;
	constituents[1].address = (uint64_t)pages + PAGE_SIZE * 3;

	/*
	 * Specify that we now want to test the second constituent of the
	 * lent memory region.
	 */
	pages[PAGE_SIZE] = 1;

	/* Use the secondary VM for this test as the first is now aborted. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM2, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}

/**
 * SPCI: Verify past the lower bound of the lent region cannot be accessed.
 */
TEST(memory_sharing, spci_lend_check_lower_bounds)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();
	uint8_t *ptr = pages;
	uint32_t msg_size;

	SERVICE_SELECT(SERVICE_VM1, "spci_lend_check_lower_bound", mb.send);
	SERVICE_SELECT(SERVICE_VM2, "spci_lend_check_lower_bound", mb.send);

	/* Initialise the memory before lending it. */
	memset_s(ptr, sizeof(pages), 'b', 4 * PAGE_SIZE);

	/* Specify non-contiguous memory regions. */
	struct spci_memory_region_constituent constituents[] = {
		{.address = (uint64_t)pages, .page_count = 1},
		{.address = (uint64_t)pages + PAGE_SIZE * 2, .page_count = 1},
	};

	/*
	 * Specify that we want to test the first constituent of the lent
	 * memory region. This is utilised by the test service.
	 */
	pages[0] = 0;

	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM1, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);

	/* Use different memory regions for verifying the second constituent. */
	constituents[0].address = (uint64_t)pages + PAGE_SIZE * 1;
	constituents[1].address = (uint64_t)pages + PAGE_SIZE * 3;

	/*
	 * Specify that we now want to test the second constituent of the
	 * lent memory region.
	 */
	pages[PAGE_SIZE] = 1;

	/* Use the secondary VM for this test as the first is now aborted. */
	msg_size = spci_memory_region_init(
		mb.send, HF_PRIMARY_VM_ID, SERVICE_VM2, constituents,
		ARRAY_SIZE(constituents), 0, 0, SPCI_MEMORY_RW_X,
		SPCI_MEMORY_NORMAL_MEM, SPCI_MEMORY_CACHE_WRITE_BACK,
		SPCI_MEMORY_OUTER_SHAREABLE);
	EXPECT_EQ(spci_mem_lend(msg_size, msg_size, 0).func, SPCI_SUCCESS_32);

	run_res = spci_run(SERVICE_VM2, 0);
	EXPECT_EQ(exception_handler_receive_exception_count(&run_res, mb.recv),
		  1);
}
