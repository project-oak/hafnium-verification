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

#include "hf/arch/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

TEST_SERVICE(relay)
{
	/*
	 * Loop, forward messages to the next VM.
	 *
	 * The first 32-bits of the message are the little-endian 32-bit ID of
	 * the VM to forward the message to. This ID will be dropped from the
	 * message so multiple IDs can be places at the start of the message.
	 */
	for (;;) {
		uint32_t *chain;
		uint32_t next_vm_id;
		void *next_message;
		uint32_t next_message_size;

		/* Receive the message to relay. */
		struct hf_mailbox_receive_return res = hf_mailbox_receive(true);
		ASSERT_GE(res.size, sizeof(uint32_t));

		/* Prepare to relay the message. */
		chain = SERVICE_RECV_BUFFER();
		next_vm_id = le32toh(*chain);
		next_message = chain + 1;
		next_message_size = res.size - sizeof(uint32_t);

		/* Send the message to the next stage. */
		memcpy(SERVICE_SEND_BUFFER(), next_message, next_message_size);
		hf_mailbox_clear();
		hf_mailbox_send(next_vm_id, next_message_size, false);
	}
}
