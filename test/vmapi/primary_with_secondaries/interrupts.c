/*
 * Copyright 2019 Google LLC
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

#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"

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
