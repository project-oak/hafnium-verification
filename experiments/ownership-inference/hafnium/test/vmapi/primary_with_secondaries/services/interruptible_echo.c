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
#include "hf/arch/vm/interrupts.h"

#include "hf/dlog.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "primary_with_secondary.h"
#include "test/hftest.h"

static void irq(void)
{
	/* Clear the interrupt. */
	hf_interrupt_get();
}

TEST_SERVICE(interruptible_echo)
{
	exception_setup(irq, NULL);
	hf_interrupt_enable(EXTERNAL_INTERRUPT_ID_A, true);
	arch_irq_enable();

	for (;;) {
		struct spci_value res = spci_msg_wait();
		void *message = SERVICE_SEND_BUFFER();
		void *recv_message = SERVICE_RECV_BUFFER();

		/* Retry if interrupted but made visible with the yield. */
		while (res.func == SPCI_ERROR_32 &&
		       res.arg2 == SPCI_INTERRUPTED) {
			spci_yield();
			res = spci_msg_wait();
		}

		ASSERT_EQ(res.func, SPCI_MSG_SEND_32);
		memcpy_s(message, SPCI_MSG_PAYLOAD_MAX, recv_message,
			 spci_msg_send_size(res));

		EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);
		spci_msg_send(SERVICE_VM1, HF_PRIMARY_VM_ID,
			      spci_msg_send_size(res), 0);
	}
}
