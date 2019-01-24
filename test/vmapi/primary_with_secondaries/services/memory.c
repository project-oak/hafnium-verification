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
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

alignas(PAGE_SIZE) static uint8_t page[PAGE_SIZE];

TEST_SERVICE(memory_increment)
{
	/* Loop, writing message to the shared memory. */
	for (;;) {
		struct hf_mailbox_receive_return res = hf_mailbox_receive(true);
		uint8_t *ptr;
		size_t i;

		/* Check the memory was cleared. */
		memcpy(&ptr, SERVICE_RECV_BUFFER(), sizeof(ptr));
		for (int i = 0; i < PAGE_SIZE; ++i) {
			ASSERT_EQ(ptr[i], 0);
		}

		/* Allow the memory to be populated. */
		hf_vcpu_yield();

		/* Increment each byte of memory. */
		for (i = 0; i < PAGE_SIZE; ++i) {
			++ptr[i];
		}

		/* Signal completion and reset. */
		hf_mailbox_clear();
		hf_mailbox_send(res.vm_id, 0, false);
	}
}

TEST_SERVICE(memory_return)
{
	/* Loop, giving memory back to the sender. */
	for (;;) {
		struct hf_mailbox_receive_return res = hf_mailbox_receive(true);
		uint8_t *ptr;

		/* Check the memory was cleared. */
		memcpy(&ptr, SERVICE_RECV_BUFFER(), sizeof(ptr));
		for (int i = 0; i < PAGE_SIZE; ++i) {
			ASSERT_EQ(ptr[i], 0);
		}

		/* Give the memory back and notify the sender. */
		ASSERT_EQ(hf_share_memory(res.vm_id, (hf_ipaddr_t)ptr,
					  PAGE_SIZE, HF_MEMORY_GIVE),
			  0);
		hf_mailbox_clear();
		hf_mailbox_send(res.vm_id, 0, false);

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
	memcpy(SERVICE_SEND_BUFFER(), &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(HF_PRIMARY_VM_ID, sizeof(ptr), false), 0);

	/* Try using the memory that isn't valid unless it's been returned.  */
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
	memcpy(SERVICE_SEND_BUFFER(), &ptr, sizeof(ptr));
	EXPECT_EQ(hf_mailbox_send(HF_PRIMARY_VM_ID, sizeof(ptr), false), 0);

	/* Try using the memory that isn't valid unless it's been returned.  */
	page[633] = 180;
}
