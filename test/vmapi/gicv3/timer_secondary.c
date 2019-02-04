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

#include "hf/arch/cpu.h"
#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/abi.h"
#include "hf/call.h"

#include "gicv3.h"
#include "hftest.h"

SET_UP(timer_secondary)
{
	system_setup();

	EXPECT_EQ(hf_vm_configure(send_page_addr, recv_page_addr), 0);
	SERVICE_SELECT(SERVICE_VM0, "timer", send_page);

	interrupt_enable(VIRTUAL_TIMER_IRQ, true);
	interrupt_set_edge_triggered(VIRTUAL_TIMER_IRQ, true);
	interrupt_set_priority_mask(0xff);
	arch_irq_enable();
}

static void timer_busywait_secondary()
{
	const char message[] = "loop 0099999";
	const char expected_response[] = "Got IRQ 03.";
	struct hf_vcpu_run_return run_res;

	/* Let the secondary get started and wait for our message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Send the message for the secondary to set a timer. */
	memcpy(send_page, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);

	/*
	 * Let the secondary handle the message and set the timer. It will loop
	 * until the hardware interrupt fires, at which point we'll get and
	 * ignore the interrupt, and see a HF_VCPU_RUN_YIELD return code.
	 */
	dlog("running secondary after sending timer message.\n");
	last_interrupt_id = 0;
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_PREEMPTED);
	dlog("secondary yielded after receiving timer message\n");
	EXPECT_EQ(last_interrupt_id, VIRTUAL_TIMER_IRQ);

	/*
	 * Now that the timer has expired, when we call hf_vcpu_run again
	 * Hafnium should inject a virtual timer interrupt into the secondary,
	 * which should get it and respond.
	 */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(
		memcmp(recv_page, expected_response, sizeof(expected_response)),
		0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Send a message to the interruptible VM, which will start a timer to interrupt
 * itself to send a response back.
 */
TEST(timer_secondary, busywait)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_busywait_secondary();
	timer_busywait_secondary();
}

static void timer_secondary(const char message[],
			    enum hf_vcpu_run_code expected_code)
{
	const char expected_response[] = "Got IRQ 03.";
	size_t message_length = strlen(message) + 1;
	struct hf_vcpu_run_return run_res;

	/* Let the secondary get started and wait for our message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Send the message for the secondary to set a timer. */
	memcpy(send_page, message, message_length);
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, message_length, false), 0);

	/*
	 * Let the secondary handle the message and set the timer. Then there's
	 * a race for whether it manages to block and switch to the primary
	 * before the hardware timer fires, so we need to handle both cases.
	 */
	last_interrupt_id = 0;
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	if (run_res.code == expected_code) {
		/*
		 * This case happens if the secondary manages to block and
		 * switch to the primary before the timer fires.
		 */
		dlog("secondary sleeping after receiving timer message\n");
		/* Loop until the timer fires. */
		while (run_res.code == expected_code) {
			dlog("Primary looping until timer fires\n");
			if (expected_code == HF_VCPU_RUN_WAIT_FOR_INTERRUPT ||
			    expected_code == HF_VCPU_RUN_WAIT_FOR_MESSAGE) {
				EXPECT_NE(run_res.sleep.ns,
					  HF_SLEEP_INDEFINITE);
				dlog("%d ns remaining\n", run_res.sleep.ns);
			}
			run_res = hf_vcpu_run(SERVICE_VM0, 0);
		}
		dlog("Primary done looping\n");
	} else if (run_res.code == HF_VCPU_RUN_PREEMPTED) {
		/*
		 * This case happens if the (hardware) timer fires before the
		 * secondary blocks and switches to the primary. Then we get the
		 * interrupt to the primary, ignore it, and see a
		 * HF_VCPU_RUN_PREEMPTED code from the hf_vcpu_run call, so we
		 * should call it again for the timer interrupt to be injected
		 * automatically by Hafnium.
		 */
		EXPECT_EQ(last_interrupt_id, VIRTUAL_TIMER_IRQ);
		dlog("Preempted by timer interrupt, running again\n");
		run_res = hf_vcpu_run(SERVICE_VM0, 0);
	} else {
		/* No other return codes should occur here, so fail. */
		FAIL("Unexpected run result code (%d).", run_res.code);
	}

	/* Once we wake it up it should get the timer interrupt and respond. */
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_MESSAGE);
	EXPECT_EQ(run_res.message.size, sizeof(expected_response));
	EXPECT_EQ(
		memcmp(recv_page, expected_response, sizeof(expected_response)),
		0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}

/**
 * Send a message to the interruptible VM, which will start a timer to interrupt
 * itself to send a response back. This test is run with both long and short
 * timer lengths, to try to cover both cases of the race for whether the timer
 * fires before or after the secondary VM blocks and switches back to the
 * primary.
 */
TEST(timer_secondary, wfi_short)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("WFI  0000001", HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
	timer_secondary("WFI  0000001", HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
}

TEST(timer_secondary, wfi_long)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("WFI  0099999", HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
	timer_secondary("WFI  0099999", HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
}

TEST(timer_secondary, wfe_short)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("WFE  0000001", HF_VCPU_RUN_YIELD);
	timer_secondary("WFE  0000001", HF_VCPU_RUN_YIELD);
}

TEST(timer_secondary, wfe_long)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("WFE  0099999", HF_VCPU_RUN_YIELD);
	timer_secondary("WFE  0099999", HF_VCPU_RUN_YIELD);
}

TEST(timer_secondary, receive_short)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("RECV 0000001", HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	timer_secondary("RECV 0000001", HF_VCPU_RUN_WAIT_FOR_MESSAGE);
}

TEST(timer_secondary, receive_long)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("RECV 0099999", HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	timer_secondary("RECV 0099999", HF_VCPU_RUN_WAIT_FOR_MESSAGE);
}

/**
 * Set the timer for a very long time, and expect that it doesn't fire.
 */
TEST(timer_secondary, wfi_very_long)
{
	const char message[] = "WFI  9999999";
	size_t message_length = strlen(message) + 1;
	struct hf_vcpu_run_return run_res;

	/* Let the secondary get started and wait for our message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_MESSAGE);
	EXPECT_EQ(run_res.sleep.ns, HF_SLEEP_INDEFINITE);

	/* Send the message for the secondary to set a timer. */
	memcpy(send_page, message, message_length);
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, message_length, false), 0);

	/*
	 * Let the secondary handle the message and set the timer.
	 */
	last_interrupt_id = 0;
	for (int i = 0; i < 20; ++i) {
		run_res = hf_vcpu_run(SERVICE_VM0, 0);
		EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);
		dlog("Primary looping until timer fires; %d ns "
		     "remaining\n",
		     run_res.sleep.ns);
	}
}
