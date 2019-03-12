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

#include "hf/arch/vm/timer.h"

#include "hf/arch/cpu.h"
#include "hf/arch/std.h"
#include "hf/arch/vm/events.h"
#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/dlog.h"

#include "vmapi/hf/call.h"

#include "common.h"
#include "hftest.h"

/*
 * Secondary VM that sets timers in response to messages, and sends messages
 * back when they fire.
 */

static volatile bool timer_fired = false;

static void irq_current(void)
{
	uint32_t interrupt_id = hf_interrupt_get();
	char buffer[] = "Got IRQ xx.";
	int size = sizeof(buffer);
	dlog("secondary IRQ %d from current\n", interrupt_id);
	if (interrupt_id == HF_VIRTUAL_TIMER_INTID) {
		timer_fired = true;
	}
	buffer[8] = '0' + interrupt_id / 10;
	buffer[9] = '0' + interrupt_id % 10;
	memcpy(SERVICE_SEND_BUFFER()->payload, buffer, size);
	spci_message_init(SERVICE_SEND_BUFFER(), size, HF_PRIMARY_VM_ID,
			  SERVICE_RECV_BUFFER()->target_vm_id);
	spci_msg_send(0);
	dlog("secondary IRQ %d ended\n", interrupt_id);
	event_send_local();
}

TEST_SERVICE(timer)
{
	exception_setup(irq_current);
	hf_interrupt_enable(HF_VIRTUAL_TIMER_INTID, true);
	arch_irq_enable();

	for (;;) {
		const char timer_wfi_message[] = "**** xxxxxxx";
		struct spci_message *message_header = SERVICE_RECV_BUFFER();
		uint8_t *message;
		bool wfi, wfe, receive;
		bool disable_interrupts;
		uint32_t ticks;
		mailbox_receive_retry();

		if (message_header->source_vm_id != HF_PRIMARY_VM_ID ||
		    message_header->length != sizeof(timer_wfi_message)) {
			FAIL("Got unexpected message from VM %d, size %d.\n",
			     message_header->source_vm_id,
			     message_header->length);
		}

		message = message_header->payload;

		/*
		 * Start a timer to send the message back: enable it and
		 * set it for the requested number of ticks.
		 */
		wfi = memcmp(message, "WFI ", 4) == 0;
		wfe = memcmp(message, "WFE ", 4) == 0;
		receive = memcmp(message, "RECV", 4) == 0;
		disable_interrupts = wfi || receive;
		ticks = (message[5] - '0') * 1000000 +
			(message[6] - '0') * 100000 +
			(message[7] - '0') * 10000 + (message[8] - '0') * 1000 +
			(message[9] - '0') * 100 + (message[10] - '0') * 10 +
			(message[11] - '0');

		hf_mailbox_clear();

		dlog("Starting timer for %d ticks.\n", ticks);

		if (disable_interrupts) {
			arch_irq_disable();
		}

		timer_set(ticks);
		timer_start();
		dlog("Waiting for timer...\n");

		/* Wait for the timer interrupt. */
		if (wfi) {
			interrupt_wait();
		} else if (wfe) {
			while (!timer_fired) {
				event_wait();
			}
		} else if (receive) {
			int32_t res = spci_msg_recv(SPCI_MSG_RECV_BLOCK);

			EXPECT_EQ(res, SPCI_INTERRUPTED);
		} else {
			/* Busy wait until the timer fires. */
			while (!timer_fired) {
			}
		}

		if (disable_interrupts) {
			arch_irq_enable();
		}

		EXPECT_TRUE(timer_fired);
		timer_fired = false;
		dlog("Done waiting.\n");
	}
}
