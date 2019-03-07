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

#include "../msr.h"
#include "gicv3.h"
#include "hftest.h"

/**
 * Converts a number of nanoseconds to the equivalent number of timer ticks.
 */
static uint64_t ns_to_ticks(uint64_t ns)
{
	return ns * read_msr(cntfrq_el0) / NANOS_PER_UNIT;
}

SET_UP(busy_secondary)
{
	struct hf_vcpu_run_return run_res;

	system_setup();

	/* Configure mailbox pages. */
	EXPECT_EQ(hf_vm_configure(send_page_addr, recv_page_addr), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	SERVICE_SELECT(SERVICE_VM0, "busy", send_page);
}

TEST(busy_secondary, virtual_timer)
{
	const char message[] = "loop";
	struct hf_vcpu_run_return run_res;

	interrupt_enable(VIRTUAL_TIMER_IRQ, true);
	interrupt_set_priority(VIRTUAL_TIMER_IRQ, 0x80);
	interrupt_set_edge_triggered(VIRTUAL_TIMER_IRQ, true);
	/*
	 * Hypervisor timer IRQ is needed for Hafnium to return control to the
	 * primary if the (emulated) virtual timer fires while the secondary is
	 * running.
	 */
	interrupt_enable(HYPERVISOR_TIMER_IRQ, true);
	interrupt_set_priority(HYPERVISOR_TIMER_IRQ, 0x80);
	interrupt_set_edge_triggered(HYPERVISOR_TIMER_IRQ, true);
	interrupt_set_priority_mask(0xff);
	arch_irq_enable();

	/* Let the secondary get started and wait for our message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Check that no interrupts are active or pending to start with. */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);

	dlog("Starting timer\n");
	/* Set virtual timer for 1 mS and enable. */
	write_msr(CNTV_TVAL_EL0, ns_to_ticks(1000000));
	write_msr(CNTV_CTL_EL0, 0x00000001);

	/* Let secondary start looping. */
	dlog("Telling secondary to loop.\n");
	memcpy(send_page, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_PREEMPTED);

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
	/* Check timer status. */
	EXPECT_EQ(read_msr(CNTV_CTL_EL0), 0x00000005);

	/* There should again be no pending or active interrupts. */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);
}

TEST(busy_secondary, physical_timer)
{
	const char message[] = "loop";
	struct hf_vcpu_run_return run_res;

	interrupt_enable(PHYSICAL_TIMER_IRQ, true);
	interrupt_set_priority(PHYSICAL_TIMER_IRQ, 0x80);
	interrupt_set_edge_triggered(PHYSICAL_TIMER_IRQ, true);
	interrupt_set_priority_mask(0xff);
	arch_irq_enable();

	/* Let the secondary get started and wait for our message. */
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_WAIT_FOR_INTERRUPT);

	/* Check that no interrupts are active or pending to start with. */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);

	dlog("Starting timer\n");
	/* Set physical timer for 1 ms and enable. */
	write_msr(CNTP_TVAL_EL0, ns_to_ticks(1000000));
	write_msr(CNTP_CTL_EL0, 0x00000001);

	/* Let secondary start looping. */
	dlog("Telling secondary to loop.\n");
	memcpy(send_page, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(SERVICE_VM0, sizeof(message), false), 0);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_PREEMPTED);

	dlog("Waiting for interrupt\n");
	while (last_interrupt_id == 0) {
		EXPECT_EQ(GICD_ISPENDR(0), 0);
		EXPECT_EQ(GICR_ISPENDR0, 0);
		EXPECT_EQ(GICD_ISACTIVER(0), 0);
		EXPECT_EQ(GICR_ISACTIVER0, 0);
	}

	/* Check that we got the interrupt. */
	dlog("Checking for interrupt\n");
	EXPECT_EQ(last_interrupt_id, PHYSICAL_TIMER_IRQ);
	/* Check timer status. */
	EXPECT_EQ(read_msr(CNTP_CTL_EL0), 0x00000005);

	/* There should again be no pending or active interrupts. */
	EXPECT_EQ(GICD_ISPENDR(0), 0);
	EXPECT_EQ(GICR_ISPENDR0, 0);
	EXPECT_EQ(GICD_ISACTIVER(0), 0);
	EXPECT_EQ(GICR_ISACTIVER0, 0);
}
