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

#include "hf/arch/vm/timer.h"

#include "hf/arch/cpu.h"
#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/dlog.h"
#include "hf/std.h"

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
	memcpy(SERVICE_SEND_BUFFER(), buffer, size);
	hf_mailbox_send(HF_PRIMARY_VM_ID, size, false);
	dlog("secondary IRQ %d ended\n", interrupt_id);
}

TEST_SERVICE(timer)
{
	exception_setup(irq_current);
	hf_interrupt_enable(HF_VIRTUAL_TIMER_INTID, true);
	arch_irq_enable();

	for (;;) {
		const char timer_wfi_message[] = "WFI  xxxxxxx";
		struct hf_mailbox_receive_return received_message =
			mailbox_receive_retry();
		if (received_message.vm_id == HF_PRIMARY_VM_ID &&
		    received_message.size == sizeof(timer_wfi_message)) {
			/*
			 * Start a timer to send the message back: enable it and
			 * set it for the requested number of ticks.
			 */
			char *message = SERVICE_RECV_BUFFER();
			bool wfi = memcmp(message, timer_wfi_message, 5) == 0;
			int32_t ticks = (message[5] - '0') * 1000000 +
					(message[6] - '0') * 100000 +
					(message[7] - '0') * 10000 +
					(message[8] - '0') * 1000 +
					(message[9] - '0') * 100 +
					(message[10] - '0') * 10 +
					(message[11] - '0');
			dlog("Starting timer for %d ticks.\n", ticks);
			if (wfi) {
				arch_irq_disable();
			}
			timer_set(ticks);
			timer_start();
			dlog("Waiting for timer...\n");
			if (wfi) {
				/* WFI until the timer fires. */
				interrupt_wait();
				arch_irq_enable();
			} else {
				/* Busy wait until the timer fires. */
				while (!timer_fired) {
				}
			}
			EXPECT_TRUE(timer_fired);
			timer_fired = false;
			dlog("Done waiting.\n");
		} else {
			dlog("Got unexpected message from VM %d, size %d.\n",
			     received_message.vm_id, received_message.size);
			FAIL("Unexpected message");
		}
		hf_mailbox_clear();
	}
}
