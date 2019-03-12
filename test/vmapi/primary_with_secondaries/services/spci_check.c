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

#include "hf/arch/std.h"

#include "hf/spci.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"

TEST_SERVICE(spci_check)
{
	struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
	const char message[] = "spci_msg_send";
	struct spci_message expected_message = {
		.flags = SPCI_MESSAGE_IMPDEF_MASK,
		.length = sizeof(message),
		.target_vm_id = SERVICE_VM0,
		.source_vm_id = HF_PRIMARY_VM_ID,

		/*
		 * TODO: Padding fields may be set to MBZ in the next SPCI spec
		 * versions.
		 */
		.reserved_1 = 0,
		.reserved_2 = 0,
	};

	/* Wait for single message to be sent by the primary VM. */
	spci_msg_recv(SPCI_MSG_RECV_BLOCK);

	/* Ensure message header has all fields correctly set. */
	EXPECT_EQ(recv_buf->flags, expected_message.flags);
	EXPECT_EQ(recv_buf->length, expected_message.length);
	EXPECT_EQ(recv_buf->target_vm_id, expected_message.target_vm_id);
	EXPECT_EQ(recv_buf->source_vm_id, expected_message.source_vm_id);

	/* TODO: Padding fields may be set to MBZ in the next SPCI spec
	 * versions. */
	EXPECT_EQ(recv_buf->reserved_1, expected_message.reserved_1);
	EXPECT_EQ(recv_buf->reserved_2, expected_message.reserved_2);

	/* Ensure message header has all fields correctly set. */
	EXPECT_EQ(memcmp(recv_buf, &expected_message, sizeof(expected_message)),
		  0);

	/* Ensure that the payload was correctly transmitted. */
	EXPECT_EQ(memcmp(recv_buf->payload, message, sizeof(message)), 0);

	hf_vcpu_yield();
}
