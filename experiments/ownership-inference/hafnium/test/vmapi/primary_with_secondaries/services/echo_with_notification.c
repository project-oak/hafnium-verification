/*
 * Copyright 2018 The Hafnium Authors.
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

#include "hf/spci.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "../msr.h"
#include "test/hftest.h"

static void irq(void)
{
	hf_interrupt_get();
}

static void wait_for_vm(uint32_t vmid)
{
	for (;;) {
		int64_t w = hf_mailbox_writable_get();
		if (w == vmid) {
			return;
		}

		if (w == -1) {
			interrupt_wait();
			arch_irq_enable();
			arch_irq_disable();
		}
	}
}

TEST_SERVICE(echo_with_notification)
{
	exception_setup(irq, NULL);
	hf_interrupt_enable(HF_MAILBOX_WRITABLE_INTID, true);

	/* Loop, echo messages back to the sender. */
	for (;;) {
		void *send_buf = SERVICE_SEND_BUFFER();
		void *recv_buf = SERVICE_RECV_BUFFER();
		struct spci_value ret = spci_msg_wait();
		spci_vm_id_t target_vm_id = spci_msg_send_receiver(ret);
		spci_vm_id_t source_vm_id = spci_msg_send_sender(ret);

		memcpy_s(send_buf, SPCI_MSG_PAYLOAD_MAX, recv_buf,
			 spci_msg_send_size(ret));

		while (spci_msg_send(target_vm_id, source_vm_id,
				     spci_msg_send_size(ret),
				     SPCI_MSG_SEND_NOTIFY)
			       .func != SPCI_SUCCESS_32) {
			wait_for_vm(source_vm_id);
		}

		EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);
	}
}
