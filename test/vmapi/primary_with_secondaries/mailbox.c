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

#include <stdint.h>

#include "hf/spci.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"
#include "util.h"

/**
 * Reverses the order of the elements in the given array.
 */
static void reverse(char *s, size_t len)
{
	size_t i;

	for (i = 0; i < len / 2; i++) {
		char t = s[i];
		s[i] = s[len - 1 - i];
		s[len - 1 - i] = t;
	}
}

/**
 * Finds the next lexicographic permutation of the given array, if there is one.
 */
static void next_permutation(char *s, size_t len)
{
	size_t i, j;

	for (i = len - 2; i < len; i--) {
		const char t = s[i];
		if (t >= s[i + 1]) {
			continue;
		}

		for (j = len - 1; t >= s[j]; j--) {
		}

		s[i] = s[j];
		s[j] = t;
		reverse(s + i + 1, len - i - 1);
		return;
	}
}

/**
 * Clearing an empty mailbox is a noop.
 */
TEST(mailbox, clear_empty)
{
	EXPECT_EQ(hf_mailbox_clear(), 0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Send and receive the same message from the echo VM.
 */
TEST(mailbox, echo)
{
	const char message[] = "Echo this back to me!";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "echo", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Set the message, echo it and check it didn't change. */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, message,
		 sizeof(message));
	spci_message_init(mb.send, sizeof(message), SERVICE_VM0,
			  HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(mb.recv->length, sizeof(message));
	EXPECT_EQ(memcmp(mb.send->payload, message, sizeof(message)), 0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Repeatedly send a message and receive it back from the echo VM.
 */
TEST(mailbox, repeated_echo)
{
	char message[] = "Echo this back to me!";
	struct hf_vcpu_run_return run_res;
	uint8_t i;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "echo", mb.send);

	for (i = 0; i < 100; i++) {
		/* Run secondary until it reaches the wait for messages. */
		run_res = hf_vcpu_run(SERVICE_VM0, 0);
		EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
		EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

		/* Set the message, echo it and check it didn't change. */
		next_permutation(message, sizeof(message) - 1);
		memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, message,
			 sizeof(message));
		spci_message_init(mb.send, sizeof(message), SERVICE_VM0,
				  HF_PRIMARY_VM_ID);
		EXPECT_EQ(spci_msg_send(0), 0);
		run_res = hf_vcpu_run(SERVICE_VM0, 0);
		EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
		EXPECT_EQ(mb.recv->length, sizeof(message));
		EXPECT_EQ(memcmp(mb.recv->payload, message, sizeof(message)),
			  0);
		EXPECT_EQ(hf_mailbox_clear(), 0);
	}
}

/**
 * Send a message to relay_a which will forward it to relay_b where it will be
 * sent back here.
 */
TEST(mailbox, relay)
{
	const char message[] = "Send this round the relay!";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "relay", mb.send);
	SERVICE_SELECT(SERVICE_VM1, "relay", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);
	run_res = hf_vcpu_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/*
	 * Build the message chain so the message is sent from here to
	 * SERVICE_VM0, then to SERVICE_VM1 and finally back to here.
	 */
	{
		spci_vm_id_t *chain = (spci_vm_id_t *)mb.send->payload;
		*chain++ = htole32(SERVICE_VM1);
		*chain++ = htole32(HF_PRIMARY_VM_ID);
		memcpy_s(chain,
			 SPCI_MSG_PAYLOAD_MAX - (2 * sizeof(spci_vm_id_t)),
			 message, sizeof(message));

		spci_message_init(mb.send,
				  sizeof(message) + (2 * sizeof(spci_vm_id_t)),
				  SERVICE_VM0, HF_PRIMARY_VM_ID);
		EXPECT_EQ(spci_msg_send(0), 0);
	}

	/* Let SERVICE_VM0 forward the message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.vm_id, SERVICE_VM1);
	EXPECT_EQ(mb.recv->length, 0);

	/* Let SERVICE_VM1 forward the message. */
	run_res = hf_vcpu_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Ensure the message is intact. */
	EXPECT_EQ(run_res.message.vm_id, HF_PRIMARY_VM_ID);
	EXPECT_EQ(mb.recv->length, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv->payload, message, sizeof(message)), 0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Send a message before the secondary VM is configured, but do not register
 * for notification. Ensure we're not notified.
 */
TEST(mailbox, no_primary_to_secondary_notification_on_configure)
{
	struct hf_vcpu_run_return run_res;

	struct mailbox_buffers mb = set_up_mailbox();
	spci_message_init(mb.send, 0, SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_BUSY);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	spci_message_init(mb.send, 0, SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
}

/**
 * Send a message before the secondary VM is configured, and receive a
 * notification when it configures.
 */
TEST(mailbox, secondary_to_primary_notification_on_configure)
{
	struct hf_vcpu_run_return run_res;

	struct mailbox_buffers mb = set_up_mailbox();

	spci_message_init(mb.send, 0, SERVICE_VM0, HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(SPCI_MSG_SEND_NOTIFY), SPCI_BUSY);

	/*
	 * Run first VM for it to configure itself. It should result in
	 * notifications having to be issued.
	 */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_NOTIFY_WAITERS);

	/* A single waiter is returned. */
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), HF_PRIMARY_VM_ID);
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), -1);

	/* Send should now succeed. */
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
}

/**
 * Causes secondary VM to send two messages to primary VM. The second message
 * will reach the mailbox while it's not writable. Checks that notifications are
 * properly delivered when mailbox is cleared.
 */
TEST(mailbox, primary_to_secondary)
{
	char message[] = "not ready echo";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "echo_with_notification", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Send a message to echo service, and get response back. */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, message,
		 sizeof(message));
	spci_message_init(mb.send, sizeof(message), SERVICE_VM0,
			  HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(mb.recv->length, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv->payload, message, sizeof(message)), 0);

	/* Let secondary VM continue running so that it will wait again. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Without clearing our mailbox, send message again. */
	reverse(message, strnlen_s(message, sizeof(message)));
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, message,
		 sizeof(message));
	spci_message_init(mb.send, sizeof(message), SERVICE_VM0,
			  HF_PRIMARY_VM_ID);

	/* Message should be dropped since the mailbox was not cleared. */
	EXPECT_EQ(spci_msg_send(0), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Clear the mailbox. We expect to be told there are pending waiters. */
	EXPECT_EQ(hf_mailbox_clear(), 1);

	/* Retrieve a single waiter. */
	EXPECT_EQ(hf_mailbox_waiter_get(HF_PRIMARY_VM_ID), SERVICE_VM0);
	EXPECT_EQ(hf_mailbox_waiter_get(HF_PRIMARY_VM_ID), -1);

	/*
	 * Inject interrupt into VM and let it run again. We should receive
	 * the echoed message.
	 */
	EXPECT_EQ(
		hf_interrupt_inject(SERVICE_VM0, 0, HF_MAILBOX_WRITABLE_INTID),
		1);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(mb.recv->length, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv->payload, message, sizeof(message)), 0);
}

/**
 * Sends two messages to secondary VM without letting it run, so second message
 * won't go through. Ensure that a notification is delivered when secondary VM
 * clears the mailbox.
 */
TEST(mailbox, secondary_to_primary_notification)
{
	const char message[] = "not ready echo";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "echo_with_notification", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Send a message to echo service twice. The second should fail. */
	memcpy_s(mb.send->payload, SPCI_MSG_PAYLOAD_MAX, message,
		 sizeof(message));
	spci_message_init(mb.send, sizeof(message), SERVICE_VM0,
			  HF_PRIMARY_VM_ID);
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
	EXPECT_EQ(spci_msg_send(SPCI_MSG_SEND_NOTIFY), SPCI_BUSY);

	/* Receive a reply for the first message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(mb.recv->length, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv->payload, message, sizeof(message)), 0);

	/* Run VM again so that it clears its mailbox. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_NOTIFY_WAITERS);

	/* Retrieve a single waiter. */
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), HF_PRIMARY_VM_ID);
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), -1);

	/* Send should now succeed. */
	EXPECT_EQ(spci_msg_send(0), SPCI_SUCCESS);
}
