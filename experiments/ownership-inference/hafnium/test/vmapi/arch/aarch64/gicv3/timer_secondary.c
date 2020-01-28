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

#include "hf/arch/irq.h"
#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/abi.h"
#include "hf/call.h"
#include "hf/spci.h"

#include "gicv3.h"
#include "test/hftest.h"
#include "test/vmapi/spci.h"

SET_UP(timer_secondary)
{
	system_setup();

	EXPECT_EQ(spci_rxtx_map(send_page_addr, recv_page_addr).func,
		  SPCI_SUCCESS_32);
	SERVICE_SELECT(SERVICE_VM1, "timer", send_buffer);

	interrupt_enable(VIRTUAL_TIMER_IRQ, true);
	interrupt_set_edge_triggered(VIRTUAL_TIMER_IRQ, true);
	interrupt_set_priority_mask(0xff);
	arch_irq_enable();
}

TEAR_DOWN(timer_secondary)
{
	EXPECT_SPCI_ERROR(spci_rx_release(), SPCI_DENIED);
}

static void timer_busywait_secondary()
{
	const char message[] = "loop 0099999";
	const char expected_response[] = "Got IRQ 03.";
	struct spci_value run_res;

	/* Let the secondary get started and wait for our message. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_WAIT_32);
	EXPECT_EQ(run_res.arg2, SPCI_SLEEP_INDEFINITE);

	/* Send the message for the secondary to set a timer. */
	memcpy_s(send_buffer, SPCI_MSG_PAYLOAD_MAX, message, sizeof(message));
	EXPECT_EQ(
		spci_msg_send(HF_PRIMARY_VM_ID, SERVICE_VM1, sizeof(message), 0)
			.func,
		SPCI_SUCCESS_32);

	/*
	 * Let the secondary handle the message and set the timer. It will loop
	 * until the hardware interrupt fires, at which point we'll get and
	 * ignore the interrupt, and see a SPCI_YIELD return code.
	 */
	dlog("running secondary after sending timer message.\n");
	last_interrupt_id = 0;
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_INTERRUPT_32);
	dlog("secondary yielded after receiving timer message\n");
	EXPECT_EQ(last_interrupt_id, VIRTUAL_TIMER_IRQ);

	/*
	 * Now that the timer has expired, when we call spci_run again Hafnium
	 * should inject a virtual timer interrupt into the secondary, which
	 * should get it and respond.
	 */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_SEND_32);
	EXPECT_EQ(spci_msg_send_size(run_res), sizeof(expected_response));
	EXPECT_EQ(memcmp(recv_buffer, expected_response,
			 sizeof(expected_response)),
		  0);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);
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

static void timer_secondary(const char message[], uint64_t expected_code)
{
	const char expected_response[] = "Got IRQ 03.";
	size_t message_length = strnlen_s(message, 64) + 1;
	struct spci_value run_res;

	/* Let the secondary get started and wait for our message. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_WAIT_32);
	EXPECT_EQ(run_res.arg2, SPCI_SLEEP_INDEFINITE);

	/* Send the message for the secondary to set a timer. */
	memcpy_s(send_buffer, SPCI_MSG_PAYLOAD_MAX, message, message_length);
	EXPECT_EQ(
		spci_msg_send(HF_PRIMARY_VM_ID, SERVICE_VM1, message_length, 0)
			.func,
		SPCI_SUCCESS_32);

	/* Let the secondary handle the message and set the timer. */
	last_interrupt_id = 0;
	run_res = spci_run(SERVICE_VM1, 0);

	/*
	 * There's a race for whether the secondary manages to block and switch
	 * to the primary before the hardware timer fires, so we need to handle
	 * three cases:
	 * 1. The (hardware) timer fires immediately, we get SPCI_INTERRUPT.
	 * 2. The secondary blocks and switches back, we get expected_code until
	 *   the timer fires.
	 *  2a. The timer then expires while we are in the primary, so Hafnium
	 *   can inject the timer interrupt the next time we call spci_run.
	 *  2b. The timer fires while the secondary is running, so we get
	 *   SPCI_INTERRUPT as in case 1.
	 */

	if (run_res.func != expected_code &&
	    run_res.func != SPCI_INTERRUPT_32) {
		FAIL("Expected run to return SPCI_INTERRUPT or %#x, but "
		     "got %#x",
		     expected_code, run_res.func);
	}

	/* Loop until the timer fires. */
	while (run_res.func == expected_code) {
		/*
		 * This case happens if the secondary manages to block and
		 * switch to the primary before the timer fires.
		 */
		dlog("Primary looping until timer fires\n");
		if (expected_code == HF_SPCI_RUN_WAIT_FOR_INTERRUPT ||
		    expected_code == SPCI_MSG_WAIT_32) {
			EXPECT_NE(run_res.arg2, SPCI_SLEEP_INDEFINITE);
			dlog("%d ns remaining\n", run_res.arg2);
		}
		run_res = spci_run(SERVICE_VM1, 0);
	}
	dlog("Primary done looping\n");

	if (run_res.func == SPCI_INTERRUPT_32) {
		/*
		 * This case happens if the (hardware) timer fires before the
		 * secondary blocks and switches to the primary, either
		 * immediately after setting the timer or during the loop above.
		 * Then we get the interrupt to the primary, ignore it, and see
		 * a SPCI_INTERRUPT code from the spci_run call, so we should
		 * call it again for the timer interrupt to be injected
		 * automatically by Hafnium.
		 */
		EXPECT_EQ(last_interrupt_id, VIRTUAL_TIMER_IRQ);
		dlog("Preempted by timer interrupt, running again\n");
		run_res = spci_run(SERVICE_VM1, 0);
	}

	/* Once we wake it up it should get the timer interrupt and respond. */
	EXPECT_EQ(run_res.func, SPCI_MSG_SEND_32);
	EXPECT_EQ(spci_msg_send_size(run_res), sizeof(expected_response));
	EXPECT_EQ(memcmp(recv_buffer, expected_response,
			 sizeof(expected_response)),
		  0);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);
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
	timer_secondary("WFI  0000001", HF_SPCI_RUN_WAIT_FOR_INTERRUPT);
	timer_secondary("WFI  0000001", HF_SPCI_RUN_WAIT_FOR_INTERRUPT);
}

TEST(timer_secondary, wfi_long)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("WFI  0099999", HF_SPCI_RUN_WAIT_FOR_INTERRUPT);
	timer_secondary("WFI  0099999", HF_SPCI_RUN_WAIT_FOR_INTERRUPT);
}

TEST(timer_secondary, wfe_short)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("WFE  0000001", SPCI_YIELD_32);
	timer_secondary("WFE  0000001", SPCI_YIELD_32);
}

TEST(timer_secondary, wfe_long)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("WFE  0099999", SPCI_YIELD_32);
	timer_secondary("WFE  0099999", SPCI_YIELD_32);
}

TEST(timer_secondary, receive_short)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("RECV 0000001", SPCI_MSG_WAIT_32);
	timer_secondary("RECV 0000001", SPCI_MSG_WAIT_32);
}

TEST(timer_secondary, receive_long)
{
	/*
	 * Run the test twice in a row, to check that the state doesn't get
	 * messed up.
	 */
	timer_secondary("RECV 0099999", SPCI_MSG_WAIT_32);
	timer_secondary("RECV 0099999", SPCI_MSG_WAIT_32);
}

/**
 * Set the timer for a very long time, and expect that it doesn't fire.
 */
TEST(timer_secondary, wfi_very_long)
{
	const char message[] = "WFI  9999999";
	size_t message_length = strnlen_s(message, 64) + 1;
	struct spci_value run_res;

	/* Let the secondary get started and wait for our message. */
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_WAIT_32);
	EXPECT_EQ(run_res.arg2, SPCI_SLEEP_INDEFINITE);

	/* Send the message for the secondary to set a timer. */
	memcpy_s(send_buffer, SPCI_MSG_PAYLOAD_MAX, message, message_length);
	EXPECT_EQ(
		spci_msg_send(HF_PRIMARY_VM_ID, SERVICE_VM1, message_length, 0)
			.func,
		SPCI_SUCCESS_32);

	/*
	 * Let the secondary handle the message and set the timer.
	 */
	last_interrupt_id = 0;
	for (int i = 0; i < 20; ++i) {
		run_res = spci_run(SERVICE_VM1, 0);
		EXPECT_EQ(run_res.func, HF_SPCI_RUN_WAIT_FOR_INTERRUPT);
		dlog("Primary looping until timer fires; %d ns "
		     "remaining\n",
		     run_res.arg2);
	}
}
