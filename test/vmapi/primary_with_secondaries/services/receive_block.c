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

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"

/*
 * Secondary VM that enables an interrupt, disables interrupts globally, and
 * calls hf_mailbox_receive with block=true but expects it to fail.
 */

static void irq(void)
{
	uint32_t interrupt_id = hf_interrupt_get();
	dlog("Unexpected secondary IRQ %d from current\n", interrupt_id);
	FAIL("Unexpected secondary IRQ");
}

TEST_SERVICE(receive_block)
{
	int32_t i;
	const char message[] = "Done waiting";

	exception_setup(irq);
	arch_irq_disable();
	hf_interrupt_enable(EXTERNAL_INTERRUPT_ID_A, true);

	for (i = 0; i < 10; ++i) {
		struct hf_mailbox_receive_return res = hf_mailbox_receive(true);
		EXPECT_EQ(res.vm_id, HF_INVALID_VM_ID);
		EXPECT_EQ(res.size, 0);
	}

	memcpy(SERVICE_SEND_BUFFER(), message, sizeof(message));
	hf_mailbox_send(HF_PRIMARY_VM_ID, sizeof(message), false);
}
