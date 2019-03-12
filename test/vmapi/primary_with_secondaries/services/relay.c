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
		spci_msg_recv(SPCI_MSG_RECV_BLOCK);

		/* Prepare to relay the message. */
		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		ASSERT_GE(recv_buf->length, sizeof(uint32_t));

		chain = (uint32_t *)recv_buf->payload;
		next_vm_id = le32toh(*chain);
		next_message = chain + 1;
		next_message_size = recv_buf->length - sizeof(uint32_t);

		/* Send the message to the next stage. */
		memcpy(send_buf->payload, next_message, next_message_size);
		spci_message_init(send_buf, next_message_size, next_vm_id,
				  hf_vm_get_id());

		hf_mailbox_clear();
		spci_msg_send(0);
	}
}
