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

#include "hf/dlog.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"

static void irq(void)
{
	/* Clear the interrupt. */
	hf_interrupt_get();
}

TEST_SERVICE(interruptible_echo)
{
	exception_setup(irq);
	hf_interrupt_enable(EXTERNAL_INTERRUPT_ID_A, true);
	arch_irq_enable();

	for (;;) {
		uint32_t res = spci_msg_recv(SPCI_MSG_RECV_BLOCK);
		struct spci_message *message = SERVICE_SEND_BUFFER();
		struct spci_message *recv_message = SERVICE_RECV_BUFFER();

		/* Retry if interrupted but made visible with the yield. */
		while (res == SPCI_INTERRUPTED) {
			spci_yield();
			res = spci_msg_recv(SPCI_MSG_RECV_BLOCK);
		}

		memcpy_s(message->payload, SPCI_MSG_PAYLOAD_MAX,
			 recv_message->payload, recv_message->length);
		spci_message_init(message, recv_message->length,
				  HF_PRIMARY_VM_ID, SERVICE_VM0);

		hf_mailbox_clear();
		spci_msg_send(0);
	}
}
