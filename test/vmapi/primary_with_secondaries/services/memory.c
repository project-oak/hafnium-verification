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
	}
}
