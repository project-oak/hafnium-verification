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

#include "gicv3.h"

#include "hf/arch/cpu.h"
#include "hf/arch/std.h"
#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/dlog.h"
#include "hf/mm.h"

#include "vmapi/hf/call.h"

#include "../msr.h"
#include "hftest.h"

alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];

hf_ipaddr_t send_page_addr = (hf_ipaddr_t)send_page;
hf_ipaddr_t recv_page_addr = (hf_ipaddr_t)recv_page;

volatile uint32_t last_interrupt_id = 0;

static void irq(void)
{
	uint32_t interrupt_id = interrupt_get_and_acknowledge();
	dlog("primary IRQ %d from current\n", interrupt_id);
	last_interrupt_id = interrupt_id;
	interrupt_end(interrupt_id);
	dlog("primary IRQ %d ended\n", interrupt_id);
}

void system_setup()
{
	exception_setup(irq);
	interrupt_gic_setup();
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
