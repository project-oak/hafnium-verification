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

#include <stdalign.h>
#include <stdint.h>

#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"

/**
 * Reverses the order of the elements in the given array.
 */
void reverse(char *s, size_t len)
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
void next_permutation(char *s, size_t len)
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
 * Send and receive the same message from the echo VM.
 */
TEST(mailbox, echo)
{
	const char message[] = "Echo this back to me!";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "echo", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Set the message, echo it and check it didn't change. */
	memcpy(mb.send, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv, message, sizeof(message)), 0);
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
		EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

		/* Set the message, echo it and check it didn't change. */
		next_permutation(message, sizeof(message) - 1);
		memcpy(mb.send, message, sizeof(message));
		EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false),
			  0);
		run_res = hf_vcpu_run(SERVICE_VM0, 0);
		EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
		EXPECT_EQ(run_res.message.size, sizeof(message));
		EXPECT_EQ(memcmp(mb.recv, message, sizeof(message)), 0);
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
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
	run_res = hf_vcpu_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/*
	 * Build the message chain so the message is sent from here to
	 * SERVICE_VM0, then to SERVICE_VM1 and finally back to here.
	 */
	{
		uint32_t *chain = mb.send;
		*chain++ = htole32(SERVICE_VM1);
		*chain++ = htole32(HF_PRIMARY_VM_ID);
		memcpy(chain, message, sizeof(message));
		EXPECT_EQ(hf_mailbox_send(
				  SERVICE_VM0,
				  sizeof(message) + (2 * sizeof(uint32_t)),
				  false),
			  0);
	}

	/* Let SERVICE_VM0 forward the message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAKE_UP);
	EXPECT_EQ(run_res.wake_up.vm_id, SERVICE_VM1);
	EXPECT_EQ(run_res.wake_up.vcpu, 0);

	/* Let SERVICE_VM1 forward the message. */
	run_res = hf_vcpu_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);

	/* Ensure the message is in tact. */
	EXPECT_EQ(run_res.message.size, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv, message, sizeof(message)), 0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Send a message before the secondary VM is configured, but do not register
 * for notification. Ensure we're not notified.
 */
TEST(mailbox, no_primary_to_secondary_notification_on_configure)
{
	struct hf_vcpu_run_return run_res;

	set_up_mailbox();

	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, 0, false), -1);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, 0, false), 0);
}

/**
 * Send a message before the secondary VM is configured, and receive a
 * notification when it configures.
 */
TEST(mailbox, secondary_to_primary_notification_on_configure)
{
	struct hf_vcpu_run_return run_res;

	set_up_mailbox();

	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, 0, true), -1);

	/*
	 * Run first VM for it to configure itself. It should result in
	 * notifications having to be issued.
	 */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_NOTIFY_WAITERS);

	/* A single waiter is returned. */
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), HF_PRIMARY_VM_ID);
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), -1);

	/* Send should succeed now, though no vCPU is blocked waiting for it. */
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, 0, false), HF_INVALID_VCPU);
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
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Send a message to echo service, and get response back. */
	memcpy(mb.send, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv, message, sizeof(message)), 0);

	/* Let secondary VM continue running so that it will wait again. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Without clearing our mailbox, send message again. */
	reverse(message, strlen(message));
	memcpy(mb.send, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Clear the mailbox. We expect to be told there are pending waiters. */
	EXPECT_EQ(hf_mailbox_clear(), 1);

	/* Retrieve two waiters. */
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
	EXPECT_EQ(run_res.message.size, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv, message, sizeof(message)), 0);
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
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Send a message to echo service twice. The second should fail. */
	memcpy(mb.send, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), true), -1);

	/* Receive a reply for the first message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(message));
	EXPECT_EQ(memcmp(mb.recv, message, sizeof(message)), 0);

	/* Run VM again so that it clears its mailbox. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_NOTIFY_WAITERS);

	/* Retrieve two waiters. */
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), HF_PRIMARY_VM_ID);
	EXPECT_EQ(hf_mailbox_waiter_get(SERVICE_VM0), -1);

	/* Send should succeed now, though no vCPU is blocked waiting for it. */
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, 0, false), HF_INVALID_VCPU);
}

/**
 * Send a message to the interruptible VM, which will interrupt itself to send a
 * response back.
 */
TEST(interrupts, interrupt_self)
{
	const char message[] = "Ping";
	const char expected_response[] = "Got IRQ 05.";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "interruptible", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Set the message, echo it and wait for a response. */
	memcpy(mb.send, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(memcmp(mb.recv, expected_response, sizeof(expected_response)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Inject an interrupt to the interrupt VM, which will send a message back.
 * Repeat this twice to make sure it doesn't get into a bad state after the
 * first one.
 */
TEST(interrupts, inject_interrupt_twice)
{
	const char expected_response[] = "Got IRQ 07.";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "interruptible", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Inject the interrupt and wait for a message. */
	hf_interrupt_inject(SERVICE_VM0, 0, EXTERNAL_INTERRUPT_ID_A);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(memcmp(mb.recv, expected_response, sizeof(expected_response)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);

	/* Inject the interrupt again, and wait for the same message. */
	hf_interrupt_inject(SERVICE_VM0, 0, EXTERNAL_INTERRUPT_ID_A);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(memcmp(mb.recv, expected_response, sizeof(expected_response)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Inject two different interrupts to the interrupt VM, which will send a
 * message back each time.
 */
TEST(interrupts, inject_two_interrupts)
{
	const char expected_response[] = "Got IRQ 07.";
	const char expected_response_2[] = "Got IRQ 08.";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "interruptible", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Inject the interrupt and wait for a message. */
	hf_interrupt_inject(SERVICE_VM0, 0, EXTERNAL_INTERRUPT_ID_A);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(memcmp(mb.recv, expected_response, sizeof(expected_response)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);

	/* Inject a different interrupt and wait for a different message. */
	hf_interrupt_inject(SERVICE_VM0, 0, EXTERNAL_INTERRUPT_ID_B);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response_2));
	EXPECT_EQ(memcmp(mb.recv, expected_response_2,
			 sizeof(expected_response_2)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Inject an interrupt then send a message to the interrupt VM, which will send
 * a message back each time. This is to test that interrupt injection doesn't
 * interfere with message reception.
 */
TEST(interrupts, inject_interrupt_message)
{
	const char expected_response[] = "Got IRQ 07.";
	const char message[] = "Ping";
	const char expected_response_2[] = "Got IRQ 05.";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "interruptible", mb.send);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Inject the interrupt and wait for a message. */
	hf_interrupt_inject(SERVICE_VM0, 0, EXTERNAL_INTERRUPT_ID_A);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(memcmp(mb.recv, expected_response, sizeof(expected_response)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);

	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Now send a message to the secondary. */
	memcpy(mb.send, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response_2));
	EXPECT_EQ(memcmp(mb.recv, expected_response_2,
			 sizeof(expected_response_2)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Inject an interrupt which the target VM has not enabled, and then send a
 * message telling it to enable that interrupt ID. It should then (and only
 * then) send a message back.
 */
TEST(interrupts, inject_interrupt_disabled)
{
	const char expected_response[] = "Got IRQ 09.";
	const char message[] = "Enable interrupt C";
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "interruptible", mb.send);

	/* Inject the interrupt and expect not to get a message. */
	hf_interrupt_inject(SERVICE_VM0, 0, EXTERNAL_INTERRUPT_ID_C);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
	EXPECT_EQ(hf_mailbox_clear(), -1);

	/*
	 * Now send a message to the secondary to enable the interrupt ID, and
	 * expect the response from the interrupt we sent before.
	 */
	memcpy(mb.send, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(memcmp(mb.recv, expected_response, sizeof(expected_response)),
		  0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}
