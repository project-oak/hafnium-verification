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

#include "hf/dlog.h"

#include "vmapi/hf/call.h"

#include "../msr.h"
#include "hftest.h"
#include "interrupts.h"

#define PPI_IRQ_BASE 16
#define PHYSICAL_TIMER_IRQ (PPI_IRQ_BASE + 14)
#define VIRTUAL_TIMER_IRQ (PPI_IRQ_BASE + 11)

static volatile uint32_t last_interrupt_id = 0;

void system_setup()
{
	exception_setup();
	interrupt_gic_setup();
}

void irq_current(void)
{
	uint32_t interrupt_id = interrupt_get_and_acknowledge();
	dlog("IRQ %d from current\n", interrupt_id);
	last_interrupt_id = interrupt_id;
	interrupt_end(interrupt_id);
	dlog("IRQ %d ended\n", interrupt_id);
}

/* Check that system registers are configured as we expect on startup. */
TEST(system, system_registers_enabled)
{
	/* Check that system register interface to GICv3 is enabled. */
	uint32_t expected_sre =
		1u << 2 | /* Disable IRQ bypass. */
		1u << 1 | /* Disable FIQ bypass. */
		1u << 0;  /* Enable system register interface to GICv3. */
	EXPECT_EQ(read_msr(ICC_SRE_EL1), expected_sre);
}

TEST(system, system_setup)
{
	system_setup();

	/* Should have affinity routing enabled, group 1 interrupts enabled,
	 * group 0 disabled. */
	EXPECT_EQ(GICD_CTLR & 0x13, 0x12);
	EXPECT_EQ(read_msr(ICC_CTLR_EL1) & 0xff, 0);
}

SET_UP(interrupts)
{
	system_setup();
}

TEST(interrupts, enable_sgi)
{
	/* Interrupt IDs 0 to 15 are SGIs. */
	uint8_t intid = 3;
	interrupt_set_priority_mask(0xff);
	interrupt_set_priority(intid, 0x80);
	arch_irq_enable();
	interrupt_enable_all(true);
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);

	/* Send ourselves the SGI. */
	last_interrupt_id = 0xffffffff;
	dlog("sending SGI\n");
	interrupt_send_sgi(intid, false, 0, 0, 0, 1);
	dlog("sent SGI\n");

	/* Check that we got it, and we are back to not active or pending. */
	EXPECT_EQ(last_interrupt_id, intid);
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);
}

TEST(interrupts, disable_sgi)
{
	/* Interrupt IDs 0 to 15 are SGIs. */
	uint8_t intid = 3;
	interrupt_enable_all(true);
	interrupt_enable(intid, false);
	interrupt_set_priority_mask(0xff);
	interrupt_set_priority(intid, 0x80);
	arch_irq_enable();
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);

	/* Send ourselves the SGI. */
	last_interrupt_id = 0xffffffff;
	dlog("sending SGI\n");
	interrupt_send_sgi(intid, false, 0, 0, 0, 1);
	dlog("sent SGI\n");

	/* Check that we didn't get it, but it is pending (and not active). */
	EXPECT_EQ(last_interrupt_id, 0xffffffff);
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0x1 << intid);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);
}

TEST(interrupts, physical_timer)
{
	interrupt_enable(PHYSICAL_TIMER_IRQ, true);
	interrupt_set_priority(PHYSICAL_TIMER_IRQ, 0x80);
	interrupt_set_edge_triggered(PHYSICAL_TIMER_IRQ, true);
	interrupt_set_priority_mask(0xff);
	arch_irq_enable();

	/*
	 * Check that no (SGI or PPI) interrupts are active or pending to start
	 * with.
	 */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);

	dlog("Starting timer\n");
	/* Enable physical timer. */
	write_msr(CNTP_CTL_EL0, 0x00000001);
	/* Set timer for 1 tick. */
	write_msr(CNTP_TVAL_EL0, 1);

	dlog("waiting for interrupt\n");
	while (last_interrupt_id == 0) {
		EXPECT_EQ(GICD_ISPENDR(0), 0);
		EXPECT_EQ(GICR_ISPENDR0, 0);
		EXPECT_EQ(GICD_ISACTIVER(0), 0);
		EXPECT_EQ(GICR_ISACTIVER0, 0);
	}

	/* Check that we got the interrupt. */
	dlog("Checking for interrupt\n");
	EXPECT_EQ(last_interrupt_id, PHYSICAL_TIMER_IRQ);

	/* There should again be no pending or active interrupts. */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);
}

TEST(interrupts, virtual_timer)
{
	interrupt_enable(VIRTUAL_TIMER_IRQ, true);
	interrupt_set_priority(VIRTUAL_TIMER_IRQ, 0x80);
	interrupt_set_edge_triggered(VIRTUAL_TIMER_IRQ, true);
	interrupt_set_priority_mask(0xff);
	arch_irq_enable();

	/* Check that no interrupts are active or pending to start with. */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);

	dlog("Starting timer\n");
	/* Enable virtual timer. */
	write_msr(CNTV_CTL_EL0, 0x00000001);
	/* Set timer for 1 tick. */
	write_msr(CNTV_TVAL_EL0, 1);

	dlog("Waiting for interrupt\n");
	while (last_interrupt_id == 0) {
		EXPECT_EQ(GICD_ISPENDR(0), 0);
		EXPECT_EQ(GICR_ISPENDR0, 0);
		EXPECT_EQ(GICD_ISACTIVER(0), 0);
		EXPECT_EQ(GICR_ISACTIVER0, 0);
	}

	/* Check that we got the interrupt. */
	dlog("Checking for interrupt\n");
	EXPECT_EQ(last_interrupt_id, VIRTUAL_TIMER_IRQ);

	/* There should again be no pending or active interrupts. */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);
}
