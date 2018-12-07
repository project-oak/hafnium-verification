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

#include <stdbool.h>
#include <stdint.h>

#include "hf/arch/cpu.h"

#include "hf/dlog.h"

#include "../msr.h"

extern uint8_t vector_table_el1;

void exception_setup()
{
	/* Set exception vector table. */
	write_msr(VBAR_EL1, &vector_table_el1);

	write_msr(ICC_CTLR_EL1, 0);
}

void interrupt_gic_setup()
{
	GICD_CTLR = 1u << 4    /* Enable affinity routing. */
		    | 1u << 1; /* Enable group 1 non-secure interrupts. */

	/* Mark CPU as awake. */
	GICR_WAKER &= ~(1u << 1);
	while ((GICR_WAKER & (1u << 2)) != 0) {
		dlog("Waiting for ChildrenAsleep==0\n");
	}

	/* Put interrupts into non-secure group 1. */
	dlog("GICR_IGROUPR0 was %x\n", 0xffffffff, GICR_IGROUPR0);
	GICR_IGROUPR0 = 0xffffffff;
	dlog("wrote %x to GICR_IGROUPR0, got back %x\n", 0xffffffff,
	     GICR_IGROUPR0);
	/* Enable non-secure group 1. */
	write_msr(ICC_IGRPEN1_EL1, 0x00000001);
	dlog("wrote %x to ICC_IGRPEN1_EL1, got back %x\n", 0x00000001,
	     read_msr(ICC_IGRPEN1_EL1));
}

void interrupt_enable(uint32_t intid, bool enable)
{
	if (enable) {
		GICD_ISENABLER(intid / 32) |= 1 << (intid % 32);
		if (intid < 32) {
			GICR_ISENABLER0 |= 1 << intid;
		}
	} else {
		GICD_ICENABLER(intid / 32) |= 1 << (intid % 32);
		if (intid < 32) {
			GICR_ICENABLER0 |= 1 << intid;
		}
	}
}

void interrupt_enable_all(bool enable)
{
	uint32_t i;
	if (enable) {
		GICR_ISENABLER0 = 0xffffffff;
		for (i = 0; i < 32; ++i) {
			GICD_ISENABLER(i) = 0xffffffff;
		}
	} else {
		GICR_ICENABLER0 = 0x00000000;
		for (i = 0; i < 32; ++i) {
			GICD_ICENABLER(i) = 0x00000000;
		}
	}
}

void interrupt_set_priority_mask(uint8_t min_priority)
{
	write_msr(ICC_PMR_EL1, min_priority);
}

void interrupt_set_priority(uint32_t intid, uint8_t priority)
{
	GICD_IPRIORITYR(intid) = priority;
}

void interrupt_set_edge_triggered(uint32_t intid, bool edge_triggered)
{
	uint32_t bit = 1u << (intid % 16 * 2 + 1);
	if (intid < 32) {
		if (edge_triggered) {
			GICR_ICFGR(intid / 16) |= bit;
		} else {
			GICR_ICFGR(intid / 16) &= ~bit;
		}
	} else {
		if (edge_triggered) {
			GICD_ICFGR(intid / 16) |= bit;
		} else {
			GICD_ICFGR(intid / 16) &= ~bit;
		}
	}
}

void interrupt_send_sgi(uint8_t intid, bool irm, uint8_t affinity3,
			uint8_t affinity2, uint8_t affinity1,
			uint16_t target_list)
{
	uint64_t sgi_register =
		((uint64_t)target_list) | ((uint64_t)affinity1 << 16) |
		(((uint64_t)intid & 0x0f) << 24) | ((uint64_t)affinity2 << 32) |
		((uint64_t)irm << 40) | ((uint64_t)affinity3 << 48);
	write_msr(ICC_SGI1R_EL1, sgi_register);
}

uint32_t interrupt_get_and_acknowledge()
{
	return read_msr(ICC_IAR1_EL1);
}

void interrupt_end(uint32_t intid)
{
	write_msr(ICC_EOIR1_EL1, intid);
}

void sync_current_exception(uintreg_t esr, uintreg_t elr)
{
	switch (esr >> 26) {
	case 0x25: /* EC = 100101, Data abort. */
		dlog("Data abort: pc=0x%x, esr=0x%x, ec=0x%x", elr, esr,
		     esr >> 26);
		if (!(esr & (1u << 10))) { /* Check FnV bit. */
			dlog(", far=0x%x", read_msr(far_el1));
		} else {
			dlog(", far=invalid");
		}

		dlog("\n");
		for (;;) {
			/* do nothing */
		}

	default:
		dlog("Unknown current sync exception pc=0x%x, esr=0x%x, "
		     "ec=0x%x\n",
		     elr, esr, esr >> 26);
		for (;;) {
			/* do nothing */
		}
	}
	for (;;) {
		/* do nothing */
	}
}
