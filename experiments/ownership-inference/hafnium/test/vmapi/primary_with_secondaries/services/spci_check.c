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

#include "hf/spci.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "primary_with_secondary.h"
#include "test/hftest.h"
#include "test/vmapi/spci.h"

TEST_SERVICE(spci_check)
{
	void *recv_buf = SERVICE_RECV_BUFFER();
	const char message[] = "spci_msg_send";

	/* Wait for single message to be sent by the primary VM. */
	struct spci_value ret = spci_msg_wait();

	EXPECT_EQ(ret.func, SPCI_MSG_SEND_32);

	/* Ensure message header has all fields correctly set. */
	EXPECT_EQ(spci_msg_send_size(ret), sizeof(message));
	EXPECT_EQ(spci_msg_send_receiver(ret), hf_vm_get_id());
	EXPECT_EQ(spci_msg_send_sender(ret), HF_PRIMARY_VM_ID);

	/* Ensure that the payload was correctly transmitted. */
	EXPECT_EQ(memcmp(recv_buf, message, sizeof(message)), 0);

	spci_yield();
}

TEST_SERVICE(spci_length)
{
	void *recv_buf = SERVICE_RECV_BUFFER();
	const char message[] = "this should be truncated";

	/* Wait for single message to be sent by the primary VM. */
	struct spci_value ret = spci_msg_wait();

	EXPECT_EQ(ret.func, SPCI_MSG_SEND_32);

	/* Verify the length is as expected. */
	EXPECT_EQ(16, spci_msg_send_size(ret));

	/* Check only part of the message is sent correctly. */
	EXPECT_NE(memcmp(recv_buf, message, sizeof(message)), 0);
	EXPECT_EQ(memcmp(recv_buf, message, spci_msg_send_size(ret)), 0);

	spci_yield();
}

TEST_SERVICE(spci_recv_non_blocking)
{
	/* Wait for single message to be sent by the primary VM. */
	struct spci_value ret = spci_msg_poll();

	EXPECT_SPCI_ERROR(ret, SPCI_RETRY);

	spci_yield();
}
