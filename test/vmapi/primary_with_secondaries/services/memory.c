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
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"

alignas(PAGE_SIZE) static uint8_t page[PAGE_SIZE];

TEST_SERVICE(memory_increment)
{
	/* Loop, writing message to the shared memory. */
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);
		uint8_t *ptr;
		size_t i;

		/* Check the memory was cleared. */
		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		ptr = *(uint8_t **)recv_buf->payload;
		spci_message_init(SERVICE_SEND_BUFFER(), sizeof(ptr),
				  recv_buf->source_vm_id, hf_vm_get_id());

		for (int i = 0; i < PAGE_SIZE; ++i) {
			ASSERT_EQ(ptr[i], 0);
		}

		/* Allow the memory to be populated. */
		EXPECT_EQ(spci_yield(), SPCI_SUCCESS);

		/* Increment each byte of memory. */
		for (i = 0; i < PAGE_SIZE; ++i) {
			++ptr[i];
		}

		/* Signal completion and reset. */
		hf_mailbox_clear();
		spci_msg_send(0);
	}
}

TEST_SERVICE(memory_lend_relinquish_spci)
{
	/* Loop, giving memory back to the sender. */
	for (;;) {
		spci_msg_recv(SPCI_MSG_RECV_BLOCK);
		uint8_t *ptr;

		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		struct spci_memory_region *memory_region =
			(struct spci_memory_region *)(spci_get_lend_descriptor(
							      recv_buf)
							      ->payload);

		ptr = (uint8_t *)memory_region->constituents[0].address;
		/* Relevant information read, mailbox can be cleared. */
		hf_mailbox_clear();

		/* Check that one has access to the shared region. */
		for (int i = 0; i < PAGE_SIZE; ++i) {
			ptr[i]++;
		}

		hf_mailbox_clear();
		/* Give the memory back and notify the sender. */
		spci_memory_relinquish(
			send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
			memory_region->constituents, memory_region->count, 0);
		spci_msg_send(0);

		/*
		 * Try and access the memory which will cause a fault unless the
		 * memory has been shared back again.
		 */
		ptr[0] = 123;
	}
}

TEST_SERVICE(memory_return)
{
	/* Loop, giving memory back to the sender. */
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);
		uint8_t *ptr;

		/* Check the memory was cleared. */
		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		ptr = *(uint8_t **)recv_buf->payload;
		spci_message_init(SERVICE_SEND_BUFFER(), sizeof(ptr),
				  recv_buf->source_vm_id, hf_vm_get_id());

		for (int i = 0; i < PAGE_SIZE; ++i) {
			ASSERT_EQ(ptr[i], 0);
		}

		/* Give the memory back and notify the sender. */
		ASSERT_EQ(hf_share_memory(recv_buf->source_vm_id,
					  (hf_ipaddr_t)ptr, PAGE_SIZE,
					  HF_MEMORY_GIVE),
			  0);
		hf_mailbox_clear();
		spci_msg_send(0);

		/*
		 * Try and access the memory which will cause a fault unless the
		 * memory has been shared back again.
		 */
		ptr[0] = 123;
	}
}

TEST_SERVICE(give_memory_and_fault)
{
	uint8_t *ptr = page;

	/* Give memory to the primary. */
	ASSERT_EQ(hf_share_memory(HF_PRIMARY_VM_ID, (hf_ipaddr_t)&page,
				  PAGE_SIZE, HF_MEMORY_GIVE),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(SERVICE_SEND_BUFFER()->payload, SPCI_MSG_PAYLOAD_MAX, &ptr,
		 sizeof(ptr));
	spci_message_init(SERVICE_SEND_BUFFER(), sizeof(ptr), HF_PRIMARY_VM_ID,
			  hf_vm_get_id());
	EXPECT_EQ(spci_msg_send(0), 0);

	/* Try using the memory that isn't valid unless it's been returned. */
	page[16] = 123;
}

TEST_SERVICE(lend_memory_and_fault)
{
	uint8_t *ptr = page;

	/* Lend memory to the primary. */
	ASSERT_EQ(hf_share_memory(HF_PRIMARY_VM_ID, (hf_ipaddr_t)&page,
				  PAGE_SIZE, HF_MEMORY_LEND),
		  0);

	/*
	 * TODO: the address of the memory will be part of the proper API. That
	 *       API is still to be agreed on so the address is passed
	 *       explicitly to test the mechanism.
	 */
	memcpy_s(SERVICE_SEND_BUFFER()->payload, SPCI_MSG_PAYLOAD_MAX, &ptr,
		 sizeof(ptr));
	spci_message_init(SERVICE_SEND_BUFFER(), sizeof(ptr), HF_PRIMARY_VM_ID,
			  hf_vm_get_id());
	EXPECT_EQ(spci_msg_send(0), 0);

	/* Try using the memory that isn't valid unless it's been returned. */
	page[633] = 180;
}

TEST_SERVICE(spci_memory_return)
{
	/* Loop, giving memory back to the sender. */
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);
		uint8_t *ptr;

		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		struct spci_memory_region *memory_region =
			spci_get_donated_memory_region(recv_buf);
		hf_mailbox_clear();

		ptr = (uint8_t *)memory_region->constituents[0].address;

		/* Check that one has access to the shared region. */
		for (int i = 0; i < PAGE_SIZE; ++i) {
			ptr[i]++;
		}

		/* Give the memory back and notify the sender. */
		spci_memory_donate(
			send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
			memory_region->constituents, memory_region->count, 0);
		spci_msg_send(0);

		/*
		 * Try and access the memory which will cause a fault unless the
		 * memory has been shared back again.
		 */
		ptr[0] = 123;
	}
}

TEST_SERVICE(spci_donate_check_upper_bound)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);
	uint8_t *ptr;

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_memory_region *memory_region =
		spci_get_donated_memory_region(recv_buf);
	hf_mailbox_clear();

	ptr = (uint8_t *)memory_region->constituents[0].address;

	/* Check that one cannot access out of bounds after donated region. */
	ptr[PAGE_SIZE]++;
}

TEST_SERVICE(spci_donate_check_lower_bound)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);
	uint8_t *ptr;

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_memory_region *memory_region =
		spci_get_donated_memory_region(recv_buf);
	hf_mailbox_clear();

	ptr = (uint8_t *)memory_region->constituents[0].address;

	/* Check that one cannot access out of bounds before donated region. */
	ptr[-1]++;
}

/**
 * SPCI: Attempt to donate memory and then modify.
 */
TEST_SERVICE(spci_donate_secondary_and_fault)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);
	uint8_t *ptr;

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_message *send_buf = SERVICE_SEND_BUFFER();
	struct spci_memory_region *memory_region =
		spci_get_donated_memory_region(recv_buf);
	hf_mailbox_clear();

	ptr = (uint8_t *)memory_region->constituents[0].address;

	/* Donate memory to next VM. */
	spci_memory_donate(send_buf, SERVICE_VM1, recv_buf->target_vm_id,
			   memory_region->constituents, memory_region->count,
			   0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Ensure that we are unable to modify memory any more. */
	ptr[0] = 'c';
	EXPECT_EQ(ptr[0], 'c');
	spci_yield();
}

/**
 * SPCI: Attempt to donate memory twice from VM.
 */
TEST_SERVICE(spci_donate_twice)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_message *send_buf = SERVICE_SEND_BUFFER();
	struct spci_memory_region *memory_region =
		spci_get_donated_memory_region(recv_buf);
	struct spci_memory_region_constituent constituent =
		memory_region->constituents[0];
	hf_mailbox_clear();

	/* Yield to allow attempt to re donate from primary. */
	spci_yield();

	/* Give the memory back and notify the sender. */
	spci_memory_donate(send_buf, HF_PRIMARY_VM_ID, SERVICE_VM0,
			   &constituent, memory_region->count, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Attempt to donate the memory to another VM. */
	spci_memory_donate(send_buf, SERVICE_VM1, recv_buf->target_vm_id,
			   &constituent, memory_region->count, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);

	spci_yield();
}

/**
 * SPCI: Continually receive memory, check if we have access
 * and ensure it is not changed by a third party.
 */
TEST_SERVICE(spci_memory_receive)
{
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);
		uint8_t *ptr;

		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_memory_region *memory_region =
			spci_get_donated_memory_region(recv_buf);
		hf_mailbox_clear();

		ptr = (uint8_t *)memory_region->constituents[0].address;
		ptr[0] = 'd';
		spci_yield();

		/* Ensure memory has not changed. */
		EXPECT_EQ(ptr[0], 'd');
		spci_yield();
	}
}

/**
 * SPCI: Receive memory and attempt to donate from primary VM.
 */
TEST_SERVICE(spci_donate_invalid_source)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), 0);

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_message *send_buf = SERVICE_SEND_BUFFER();
	struct spci_memory_region *memory_region =
		spci_get_donated_memory_region(recv_buf);
	hf_mailbox_clear();

	/* Give the memory back and notify the sender. */
	spci_memory_donate(send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
			   memory_region->constituents, memory_region->count,
			   0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Fail to donate the memory from the primary to VM1. */
	spci_memory_donate(send_buf, SERVICE_VM1, HF_PRIMARY_VM_ID,
			   memory_region->constituents, memory_region->count,
			   0);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
	spci_yield();
}

TEST_SERVICE(spci_memory_lend_relinquish)
{
	/* Loop, giving memory back to the sender. */
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);
		uint8_t *ptr;

		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		struct spci_memory_region *memory_region =
			(struct spci_memory_region *)(spci_get_lend_descriptor(
							      recv_buf)
							      ->payload);

		ptr = (uint8_t *)memory_region->constituents[0].address;
		/* Relevant information read, mailbox can be cleared. */
		hf_mailbox_clear();

		/* Check that one has access to the shared region. */
		for (int i = 0; i < PAGE_SIZE; ++i) {
			ptr[i]++;
		}

		hf_mailbox_clear();
		/* Give the memory back and notify the sender. */
		spci_memory_relinquish(
			send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
			memory_region->constituents, memory_region->count, 0);
		spci_msg_send(0);

		/*
		 * Try and access the memory which will cause a fault unless the
		 * memory has been shared back again.
		 */
		ptr[0] = 123;
	}
}

/**
 * SPCI: Ensure that we can't relinquish donated memory.
 */
TEST_SERVICE(spci_memory_donate_relinquish)
{
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);
		uint8_t *ptr;

		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		struct spci_memory_region *memory_region =
			spci_get_donated_memory_region(recv_buf);
		hf_mailbox_clear();

		ptr = (uint8_t *)memory_region->constituents[0].address;

		/* Check that one has access to the shared region. */
		for (int i = 0; i < PAGE_SIZE; ++i) {
			ptr[i]++;
		}
		/* Give the memory back and notify the sender. */
		spci_memory_relinquish(
			send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
			memory_region->constituents, memory_region->count, 0);
		EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);

		/* Ensure we still have access to the memory. */
		ptr[0] = 123;

		spci_yield();
	}
}

/**
 * SPCI: Receive memory and attempt to donate from primary VM.
 */
TEST_SERVICE(spci_lend_invalid_source)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_message *send_buf = SERVICE_SEND_BUFFER();
	struct spci_memory_region *memory_region =
		(struct spci_memory_region *)(spci_get_lend_descriptor(recv_buf)
						      ->payload);
	hf_mailbox_clear();

	/* Attempt to relinquish from primary VM. */
	spci_memory_relinquish(send_buf, recv_buf->target_vm_id,
			       HF_PRIMARY_VM_ID, memory_region->constituents,
			       memory_region->count, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);

	/* Give the memory back and notify the sender. */
	spci_memory_relinquish(
		send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
		memory_region->constituents, memory_region->count, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);

	/* Ensure we cannot lend from the primary to another secondary. */
	spci_memory_lend(send_buf, SERVICE_VM1, HF_PRIMARY_VM_ID,
			 memory_region->constituents, memory_region->count, 0,
			 SPCI_LEND_RW_X, SPCI_LEND_NORMAL_MEM,
			 SPCI_LEND_CACHE_WRITE_BACK, SPCI_LEND_OUTER_SHAREABLE);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
	spci_yield();
}

/**
 * SPCI: Attempt to execute an instruction from the lent memory.
 */
TEST_SERVICE(spci_memory_lend_relinquish_X)
{
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);
		uint64_t *ptr;

		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		struct spci_memory_region *memory_region =
			(struct spci_memory_region *)(spci_get_lend_descriptor(
							      recv_buf)
							      ->payload);
		hf_mailbox_clear();

		ptr = (uint64_t *)memory_region->constituents[0].address;
		/*
		 * Verify that the instruction in memory is the encoded RET
		 * instruction.
		 */
		EXPECT_EQ(*ptr, 0xD65F03C0);
		/* Try to execute instruction from the shared memory region. */
		__asm__ volatile("blr %0" ::"r"(ptr));

		/* Release the memory again. */
		spci_memory_relinquish(
			send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
			memory_region->constituents, memory_region->count, 0);
		EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
	}
}

/**
 * SPCI: Attempt to read and write to a shared page.
 */
TEST_SERVICE(spci_memory_lend_relinquish_RW)
{
	for (;;) {
		EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);
		uint8_t *ptr;

		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		struct spci_memory_region *memory_region =
			(struct spci_memory_region *)(spci_get_lend_descriptor(
							      recv_buf)
							      ->payload);
		hf_mailbox_clear();

		ptr = (uint8_t *)memory_region->constituents[0].address;

		/* Check that we have read access. */
		for (int i = 0; i < PAGE_SIZE; ++i) {
			EXPECT_EQ(ptr[i], 'b');
		}

		/* Return control to primary, to verify shared access. */
		spci_yield();

		/* Attempt to modify the memory. */
		for (int i = 0; i < PAGE_SIZE; ++i) {
			ptr[i]++;
		}

		spci_memory_relinquish(
			send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
			memory_region->constituents, memory_region->count, 0);
		EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
	}
}

/**
 * SPCI: Attempt to modify below the lower bound for the lent memory.
 */
TEST_SERVICE(spci_lend_check_lower_bound)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);
	uint8_t *ptr;

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_memory_region *memory_region =
		(struct spci_memory_region *)(spci_get_lend_descriptor(recv_buf)
						      ->payload);
	hf_mailbox_clear();

	ptr = (uint8_t *)memory_region->constituents[0].address;

	/* Check that one cannot access before donated region. */
	ptr[-1]++;
}

/**
 * SPCI: Attempt to modify above the upper bound for the lent memory.
 */
TEST_SERVICE(spci_lend_check_upper_bound)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);
	uint8_t *ptr;

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_memory_region *memory_region =
		(struct spci_memory_region *)(spci_get_lend_descriptor(recv_buf)
						      ->payload);
	hf_mailbox_clear();

	ptr = (uint8_t *)memory_region->constituents[0].address;

	/* Check that one cannot access after donated region. */
	ptr[PAGE_SIZE]++;
}

TEST_SERVICE(spci_memory_lend_twice)
{
	EXPECT_EQ(spci_msg_recv(SPCI_MSG_RECV_BLOCK), SPCI_SUCCESS);
	uint8_t *ptr;

	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	struct spci_message *send_buf = SERVICE_SEND_BUFFER();
	struct spci_memory_region *memory_region =
		(struct spci_memory_region *)(spci_get_lend_descriptor(recv_buf)
						      ->payload);
	hf_mailbox_clear();

	ptr = (uint8_t *)memory_region->constituents[0].address;

	/* Check that we have read access. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		EXPECT_EQ(ptr[i], 'b');
	}

	/* Return control to primary. */
	spci_yield();

	/* Attempt to modify the memory. */
	for (int i = 0; i < PAGE_SIZE; ++i) {
		ptr[i]++;
	}

	for (int i = 1; i < PAGE_SIZE * 2; i++) {
		memory_region->constituents[0].address = (uint64_t)ptr + i;

		/* Fail to lend the memory back to the primary. */
		spci_memory_lend(
			send_buf, SERVICE_VM1, HF_PRIMARY_VM_ID,
			memory_region->constituents, memory_region->count, 0,
			SPCI_LEND_RW_X, SPCI_LEND_NORMAL_MEM,
			SPCI_LEND_CACHE_WRITE_BACK, SPCI_LEND_OUTER_SHAREABLE);
		EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
	}

	spci_memory_relinquish(
		send_buf, HF_PRIMARY_VM_ID, recv_buf->target_vm_id,
		memory_region->constituents, memory_region->count, 0);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
}
