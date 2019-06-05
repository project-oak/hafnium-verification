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

#include "hf/arch/cpu.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "hf/addr.h"
#include "hf/std.h"

void arch_irq_disable(void)
{
	__asm__ volatile("msr DAIFSet, #0xf");
}

void arch_irq_enable(void)
{
	__asm__ volatile("msr DAIFClr, #0xf");
}

static void gic_regs_reset(struct arch_regs *r, bool is_primary)
{
#if GIC_VERSION == 3 || GIC_VERSION == 4
	uint32_t ich_hcr = 0;
	uint32_t icc_sre_el2 =
		(1u << 0) | /* SRE, enable ICH_* and ICC_* at EL2. */
		(0x3 << 1); /* DIB and DFB, disable IRQ/FIQ bypass. */

	if (is_primary) {
		icc_sre_el2 |= 1u << 3; /* Enable EL1 access to ICC_SRE_EL1. */
	} else {
		/* Trap EL1 access to GICv3 system registers. */
		ich_hcr =
			(0x1fu << 10); /* TDIR, TSEI, TALL1, TALL0, TC bits. */
	}
	r->gic.ich_hcr_el2 = ich_hcr;
	r->gic.icc_sre_el2 = icc_sre_el2;
#endif
}

void arch_regs_reset(struct arch_regs *r, bool is_primary, spci_vm_id_t vm_id,
		     cpu_id_t vcpu_id, paddr_t table)
{
	uintreg_t pc = r->pc;
	uintreg_t arg = r->r[0];
	uintreg_t hcr;
	uintreg_t cptr;
	uintreg_t cnthctl;

	memset_s(r, sizeof(*r), 0, sizeof(*r));

	r->pc = pc;
	r->r[0] = arg;

	/* TODO: Determine if we need to set TSW. */
	hcr = (1u << 31) | /* RW bit. */
	      (1u << 21) | /* TACR, trap access to ACTRL_EL1. */
	      (1u << 19) | /* TSC, trap SMC instructions. */
	      (1u << 20) | /* TIDCP, trap impl-defined funct. */
	      (1u << 2) |  /* PTW, Protected Table Walk. */
	      (1u << 0);   /* VM: enable stage-2 translation. */

	cptr = 0;
	cnthctl = 0;

	if (is_primary) {
		cnthctl |=
			(1u << 0) | /* EL1PCTEN, don't trap phys cnt access. */
			(1u << 1);  /* EL1PCEN, don't trap phys timer access. */
	} else {
		hcr |= (7u << 3) |  /* AMO, IMO, FMO bits. */
		       (1u << 9) |  /* FB bit. */
		       (1u << 10) | /* BSU bits set to inner-sh. */
		       (3u << 13);  /* TWI, TWE bits. */

		/* TODO: Trap fp access once handler logic is in place. */

		/* TODO: Investigate fpexc32_el2 for 32bit EL0 support. */
	}

	r->lazy.hcr_el2 = hcr;
	r->lazy.cptr_el2 = cptr;
	r->lazy.cnthctl_el2 = cnthctl;
	r->lazy.vttbr_el2 = pa_addr(table) | ((uint64_t)vm_id << 48);
	r->lazy.vmpidr_el2 = vcpu_id;
	/* TODO: Use constant here. */
	r->spsr = 5 |	 /* M bits, set to EL1h. */
		  (0xf << 6); /* DAIF bits set; disable interrupts. */

	gic_regs_reset(r, is_primary);
}

void arch_regs_set_pc_arg(struct arch_regs *r, ipaddr_t pc, uintreg_t arg)
{
	r->pc = ipa_addr(pc);
	r->r[0] = arg;
}

void arch_regs_set_retval(struct arch_regs *r, uintreg_t v)
{
	r->r[0] = v;
}
