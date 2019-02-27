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

#include "hf/spci.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

TEST_SERVICE(echo)
{
	/* Loop, echo messages back to the sender. */
	for (;;) {
		hf_mailbox_receive(true);
		struct spci_message *send_buf = SERVICE_SEND_BUFFER();
		struct spci_message *recv_buf = SERVICE_RECV_BUFFER();

		memcpy(send_buf->payload, recv_buf->payload, recv_buf->length);
		spci_message_init(SERVICE_SEND_BUFFER(), recv_buf->length,
				  recv_buf->source_vm_id,
				  recv_buf->target_vm_id);

		hf_mailbox_clear();
		spci_msg_send(0);
	}
}
