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

#include "hf/arch/vm/interrupts.h"

#include <stdint.h>

#include "hf/dlog.h"

#include "msr.h"
#include "test/hftest.h"

extern uint8_t vector_table_el1;
static void (*irq_callback)(void);
static bool (*exception_callback)(void);

void irq_current(void)
{
	if (irq_callback != NULL) {
		irq_callback();
	} else {
		FAIL("Got unexpected interrupt.\n");
	}
}

noreturn static bool default_sync_current_exception(void)
{
	uintreg_t esr = read_msr(esr_el1);
	uintreg_t elr = read_msr(elr_el1);

	switch (esr >> 26) {
	case 0x25: /* EC = 100101, Data abort. */
		dlog("Data abort: pc=%#x, esr=%#x, ec=%#x", elr, esr,
		     esr >> 26);
		if (!(esr & (1U << 10))) { /* Check FnV bit. */
			dlog(", far=%#x", read_msr(far_el1));
		} else {
			dlog(", far=invalid");
		}

		dlog("\n");
		break;

	default:
		dlog("Unknown current sync exception pc=%#x, esr=%#x, "
		     "ec=%#x\n",
		     elr, esr, esr >> 26);
	}

	for (;;) {
		/* do nothing */
	}
}

bool sync_exception_current(void)
{
	if (exception_callback != NULL) {
		return exception_callback();
	}
	return default_sync_current_exception();
}

void exception_setup(void (*irq)(void), bool (*exception)(void))
{
	irq_callback = irq;
	exception_callback = exception;

	/* Set exception vector table. */
	write_msr(VBAR_EL1, &vector_table_el1);
}

void interrupt_wait(void)
{
	__asm__ volatile("wfi");
}
