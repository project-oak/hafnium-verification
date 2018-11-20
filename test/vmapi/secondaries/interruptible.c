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

#include <stdalign.h>
#include <stdint.h>

#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/dlog.h"
#include "hf/mm.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "../msr.h"

/*
 * Secondary VM that sends messages in response to interrupts, and interrupts
 * itself when it receives a message.
 */

#define DESTINATION_VM_ID 0
#define SELF_INTERRUPT_ID 5

alignas(4096) uint8_t kstack[4096];

static alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
static alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];

static hf_ipaddr_t send_page_addr = (hf_ipaddr_t)send_page;
static hf_ipaddr_t recv_page_addr = (hf_ipaddr_t)recv_page;

static struct hf_mailbox_receive_return received_message;

void irq_current(void)
{
	uint32_t interrupt_id = hf_get_and_acknowledge_interrupt();
	char buffer[] = "Got IRQ xx.";
	int size = sizeof(buffer);
	dlog("IRQ %d from current\n", interrupt_id);
	buffer[8] = '0' + interrupt_id / 10;
	buffer[9] = '0' + interrupt_id % 10;
	memcpy(send_page, buffer, size);
	hf_mailbox_send(DESTINATION_VM_ID, size);
}

void kmain(void)
{
	hf_vm_configure(send_page_addr, recv_page_addr);

	exception_setup();
	hf_enable_interrupt(SELF_INTERRUPT_ID, true);
	arch_irq_enable();

	/* Loop, echo messages back to the sender. */
	for (;;) {
		received_message = hf_mailbox_receive(true);
		hf_mailbox_clear();
		/* Interrupt ourselves */
		hf_inject_interrupt(4, 0, SELF_INTERRUPT_ID);
	}
}
