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

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "hf/addr.h"

typedef uint64_t uintreg_t;

struct arch_regs {
	/* General purpose registers. */
	uintreg_t r[31];
	uintreg_t pc;
	uintreg_t spsr;

	/* TODO: We need to save virtual timer state. */
	struct {
		uintreg_t vmpidr_el2;
		uintreg_t csselr_el1;
		uintreg_t sctlr_el1;
		uintreg_t actlr_el1;
		uintreg_t cpacr_el1;
		uintreg_t ttbr0_el1;
		uintreg_t ttbr1_el1;
		uintreg_t tcr_el1;
		uintreg_t esr_el1;
		uintreg_t afsr0_el1;
		uintreg_t afsr1_el1;
		uintreg_t far_el1;
		uintreg_t mair_el1;
		uintreg_t vbar_el1;
		uintreg_t contextidr_el1;
		uintreg_t tpidr_el0;
		uintreg_t tpidrro_el0;
		uintreg_t tpidr_el1;
		uintreg_t amair_el1;
		uintreg_t cntkctl_el1;
		uintreg_t sp_el0;
		uintreg_t sp_el1;
		uintreg_t par_el1;
		uintreg_t hcr_el2;
		uintreg_t cptr_el2;
		uintreg_t cnthctl_el2;
		uintreg_t vttbr_el2;
	} lazy;
};

static inline void arch_irq_disable(void)
{
	__asm__ volatile("msr DAIFSet, #0xf");
}

static inline void arch_irq_enable(void)
{
	__asm__ volatile("msr DAIFClr, #0xf");
}

static inline void arch_regs_init(struct arch_regs *r, bool is_primary,
				  uint64_t vmid, paddr_t table, uint32_t index)
{
	uintreg_t hcr;
	uintreg_t cptr;
	uintreg_t cnthctl;

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

		cptr |= (1u << 10); /* TFP, trap fp access. */
	}

	r->lazy.hcr_el2 = hcr;
	r->lazy.cptr_el2 = cptr;
	r->lazy.cnthctl_el2 = cnthctl;
	r->lazy.vttbr_el2 = pa_addr(table) | (vmid << 48);
	r->lazy.vmpidr_el2 = index;
	/* TODO: Use constant here. */
	r->spsr = 5 |	 /* M bits, set to EL1h. */
		  (0xf << 6); /* DAIF bits set; disable interrupts. */
}

/**
 * Updates the given registers so that when a vcpu runs, it starts off at the
 * given address (pc) with the given argument.
 *
 * This function must only be called on an arch_regs that is known not be in use
 * by any other physical CPU.
 */
static inline void arch_regs_set_pc_arg(struct arch_regs *r, ipaddr_t pc,
					uintreg_t arg)
{
	r->pc = ipa_addr(pc);
	r->r[0] = arg;
}

/**
 * Updates the register holding the return value of a function.
 *
 * This function must only be called on an arch_regs that is known not be in use
 * by any other physical CPU.
 */
static inline void arch_regs_set_retval(struct arch_regs *r, uintreg_t v)
{
	r->r[0] = v;
}

void arch_regs_set_virtual_interrupt(struct arch_regs *r, bool enable);
