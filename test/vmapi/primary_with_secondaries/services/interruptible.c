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

#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/dlog.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "../msr.h"
#include "hftest.h"
#include "primary_with_secondary.h"

/*
 * Secondary VM that sends messages in response to interrupts, and interrupts
 * itself when it receives a message.
 */

void irq_current(void)
{
	uint32_t interrupt_id = hf_get_and_acknowledge_interrupt();
	char buffer[] = "Got IRQ xx.";
	int size = sizeof(buffer);
	dlog("IRQ %d from current\n", interrupt_id);
	buffer[8] = '0' + interrupt_id / 10;
	buffer[9] = '0' + interrupt_id % 10;
	memcpy(SERVICE_SEND_BUFFER(), buffer, size);
	hf_mailbox_send(HF_PRIMARY_VM_ID, size);
}

/**
 * Try to receive a message from the mailbox, blocking if necessary, and
 * retrying if interrupted.
 */
struct hf_mailbox_receive_return mailbox_receive_retry()
{
	struct hf_mailbox_receive_return received = {
		.vm_id = HF_INVALID_VM_ID,
		.size = 0,
	};
	while (received.vm_id == HF_INVALID_VM_ID && received.size == 0) {
		received = hf_mailbox_receive(true);
	}
	return received;
}

TEST_SERVICE(interruptible)
{
	uint32_t this_vm_id = hf_vm_get_id();

	exception_setup();
	hf_enable_interrupt(SELF_INTERRUPT_ID, true);
	hf_enable_interrupt(EXTERNAL_INTERRUPT_ID_A, true);
	hf_enable_interrupt(EXTERNAL_INTERRUPT_ID_B, true);
	arch_irq_enable();

	for (;;) {
		const char ping_message[] = "Ping";
		const char enable_message[] = "Enable interrupt C";
		struct hf_mailbox_receive_return received_message =
			mailbox_receive_retry();
		if (received_message.vm_id == HF_PRIMARY_VM_ID &&
		    received_message.size == sizeof(ping_message) &&
		    memcmp(SERVICE_RECV_BUFFER(), ping_message,
			   sizeof(ping_message)) == 0) {
			/* Interrupt ourselves */
			hf_inject_interrupt(this_vm_id, 0, SELF_INTERRUPT_ID);
		} else if (received_message.vm_id == HF_PRIMARY_VM_ID &&
			   received_message.size == sizeof(enable_message) &&
			   memcmp(SERVICE_RECV_BUFFER(), enable_message,
				  sizeof(enable_message)) == 0) {
			/* Enable interrupt ID C. */
			hf_enable_interrupt(EXTERNAL_INTERRUPT_ID_C, true);
		} else {
			dlog("Got unexpected message from VM %d, size %d.\n",
			     received_message.vm_id, received_message.size);
			FAIL("Unexpected message");
		}
		hf_mailbox_clear();
	}
}
