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
#include "hf/arch/std.h"
#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/dlog.h"

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
		struct hf_mailbox_receive_return res = hf_mailbox_receive(true);

		/* Retry if interrupted but made visible with the yield. */
		while (res.vm_id == HF_INVALID_VM_ID && res.size == 0) {
			hf_vcpu_yield();
			res = hf_mailbox_receive(true);
		}

		memcpy(SERVICE_SEND_BUFFER(), SERVICE_RECV_BUFFER(), res.size);
		hf_mailbox_clear();
		hf_mailbox_send(res.vm_id, res.size, false);
	}
}
