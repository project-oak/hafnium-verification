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

#include "hf/arch/vm/interrupts_gicv3.h"

#include <stdbool.h>
#include <stdint.h>

#include "hf/dlog.h"

#include "msr.h"

void interrupt_gic_setup(void)
{
	uint32_t ctlr = 1U << 4    /* Enable affinity routing. */
			| 1U << 1; /* Enable group 1 non-secure interrupts. */

	write_msr(ICC_CTLR_EL1, 0);

	io_write32(GICD_CTLR, ctlr);

	/* Mark CPU as awake. */
	io_write32(GICR_WAKER, io_read32(GICR_WAKER) & ~(1U << 1));
	while ((io_read32(GICR_WAKER) & (1U << 2)) != 0) {
		dlog("Waiting for ChildrenAsleep==0\n");
	}

	/* Put interrupts into non-secure group 1. */
	dlog("GICR_IGROUPR0 was %x\n", 0xffffffff, io_read32(GICR_IGROUPR0));
	io_write32(GICR_IGROUPR0, 0xffffffff);
	dlog("wrote %x to GICR_IGROUPR0, got back %x\n", 0xffffffff,
	     io_read32(GICR_IGROUPR0));
	/* Enable non-secure group 1. */
	write_msr(ICC_IGRPEN1_EL1, 0x00000001);
	dlog("wrote %x to ICC_IGRPEN1_EL1, got back %x\n", 0x00000001,
	     read_msr(ICC_IGRPEN1_EL1));
}

void interrupt_enable(uint32_t intid, bool enable)
{
	uint32_t index = intid / 32;
	uint32_t bit = 1U << (intid % 32);

	if (enable) {
		io_write32_array(GICD_ISENABLER, index, bit);
		if (intid < 32) {
			io_write32(GICR_ISENABLER0, bit);
		}
	} else {
		io_write32_array(GICD_ICENABLER, index, bit);
		if (intid < 32) {
			io_write32(GICR_ICENABLER0, bit);
		}
	}
}

void interrupt_enable_all(bool enable)
{
	uint32_t i;

	if (enable) {
		io_write32(GICR_ISENABLER0, 0xffffffff);
		for (i = 0; i < 32; ++i) {
			io_write32_array(GICD_ISENABLER, i, 0xffffffff);
		}
	} else {
		io_write32(GICR_ISENABLER0, 0);
		for (i = 0; i < 32; ++i) {
			io_write32_array(GICD_ISENABLER, i, 0);
		}
	}
}

void interrupt_set_priority_mask(uint8_t min_priority)
{
	write_msr(ICC_PMR_EL1, min_priority);
}

void interrupt_set_priority(uint32_t intid, uint8_t priority)
{
	io_write8_array(GICD_IPRIORITYR, intid, priority);
}

void interrupt_set_edge_triggered(uint32_t intid, bool edge_triggered)
{
	uint32_t index = intid / 16;
	uint32_t bit = 1U << (((intid % 16) * 2) + 1);

	if (intid < 32) {
		uint32_t v = io_read32_array(GICR_ICFGR, index);

		if (edge_triggered) {
			io_write32_array(GICR_ICFGR, index, v | bit);
		} else {
			io_write32_array(GICR_ICFGR, index, v & ~bit);
		}
	} else {
		uint32_t v = io_read32_array(GICD_ICFGR, index);

		if (edge_triggered) {
			io_write32_array(GICD_ICFGR, index, v | bit);
		} else {
			io_write32_array(GICD_ICFGR, index, v & ~bit);
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

uint32_t interrupt_get_and_acknowledge(void)
{
	return read_msr(ICC_IAR1_EL1);
}

void interrupt_end(uint32_t intid)
{
	write_msr(ICC_EOIR1_EL1, intid);
}
