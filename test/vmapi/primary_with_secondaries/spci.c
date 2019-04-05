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

#include <stdint.h>

#include "hf/arch/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"
#include "util.h"

/**
 * Send a message to a secondary VM which checks the validity of the received
 * header.
 */
TEST(spci, msg_send)
{
	const char message[] = "spci_msg_send";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "spci_check", mb.send);

	/* Set the payload, init the message header and send the message. */
	memcpy(mb.send->payload, message, sizeof(message));
	spci_message_init(mb.send, sizeof(message), SERVICE_VM0,
			  HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), 0);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
}

/**
 * Send a message to a secondary VM spoofing the source vm id.
 */
TEST(spci, msg_send_spoof)
{
	const char message[] = "spci_msg_send";
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "spci_check", mb.send);

	/* Set the payload, init the message header and send the message. */
	memcpy(mb.send->payload, message, sizeof(message));
	spci_message_init(mb.send, sizeof(message), SERVICE_VM0, SERVICE_VM1);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
}

/**
 * Send a message to a secondary VM with incorrect destination id.
 */
TEST(spci, spci_invalid_destination_id)
{
	const char message[] = "fail to send";
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "spci_check", mb.send);
	/* Set the payload, init the message header and send the message. */
	memcpy(mb.send->payload, message, sizeof(message));
	spci_message_init(mb.send, sizeof(message), -1, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
}

/**
 * Ensure that the length parameter is respected when sending messages.
 */
TEST(spci, spci_incorrect_length)
{
	const char message[] = "this should be truncated";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "spci_length", mb.send);

	/* Send the message and compare if truncated. */
	memcpy(mb.send->payload, message, sizeof(message));
	/* Hard code incorrect length. */
	spci_message_init(mb.send, 16, SERVICE_VM0, HF_PRIMARY_VM_ID);

	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
}

/**
 * Attempt to send a message larger than what is supported.
 */
TEST(spci, spci_large_message)
{
	const char message[] = "fail to send";
	struct mailbox_buffers mb = set_up_mailbox();

	memcpy(mb.send->payload, message, sizeof(message));
	/* Send a message that is larger than the mailbox supports (4KB). */
	spci_message_init(mb.send, 4 * 1024, SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_INVALID_PARAMETERS);
}

/**
 * Verify secondary VM non blocking recv.
 */
TEST(spci, spci_recv_non_blocking)
{
	struct mailbox_buffers mb = set_up_mailbox();
	struct hf_vcpu_run_return run_res;

	/* Check is performed in secondary vm. */
	SERVICE_SELECT(SERVICE_VM0, "spci_recv_non_blocking", mb.send);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
}
