#pragma once

#include <stdalign.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "hf/addr.h"

struct arch_regs {
	/* General purpose registers. */
	uint64_t r[31];
	uint64_t pc;
	uint64_t spsr;

	/* TODO: We need to save virtual timer state. */
	struct {
		uint64_t vmpidr_el2;
		uint64_t csselr_el1;
		uint64_t sctlr_el1;
		uint64_t actlr_el1;
		uint64_t cpacr_el1;
		uint64_t ttbr0_el1;
		uint64_t ttbr1_el1;
		uint64_t tcr_el1;
		uint64_t esr_el1;
		uint64_t afsr0_el1;
		uint64_t afsr1_el1;
		uint64_t far_el1;
		uint64_t mair_el1;
		uint64_t vbar_el1;
		uint64_t contextidr_el1;
		uint64_t tpidr_el0;
		uint64_t tpidrro_el0;
		uint64_t tpidr_el1;
		uint64_t amair_el1;
		uint64_t cntkctl_el1;
		uint64_t sp_el0;
		uint64_t sp_el1;
		uint64_t par_el1;
	} lazy;
};

static inline struct cpu *cpu(void)
{
	struct cpu *p;
	__asm volatile("mrs %0, tpidr_el2" : "=r"(p));
	return p;
}

static inline void arch_irq_disable(void)
{
	__asm volatile("msr DAIFSet, #0xf");
}

static inline void arch_irq_enable(void)
{
	__asm volatile("msr DAIFClr, #0xf");
}

static inline void arch_cpu_update(bool is_primary)
{
	uint64_t hcr;
	uint64_t cptr;
	uint64_t cnthctl;

	/* TODO: Determine if we need to set TSW. */
	hcr = (1u << 31) | /* RW bit. */
	      (1u << 21) | /* TACR, trap access to ACTRL_EL1. */
	      (1u << 19) | /* TSC, trap SMC instructions. */
	      (1u << 20) | /* TIDCP, trap impl-defined funct. */
	      (1u << 2) |  /* PTW, Protected Table Walk. */
	      (1u << 0);   /* VM: enable stage-2 translation. */

	cptr = 0;
	cnthctl = 0;

	if (!is_primary) {
		hcr |= (7u << 3) |  /* AMO, IMO, FMO bits. */
		       (1u << 9) |  /* FB bit. */
		       (1u << 10) | /* BSU bits set to inner-sh. */
		       (3u << 13);  /* TWI, TWE bits. */

		cptr |= (1u << 10); /* TFP, trap fp access. */

		cnthctl |= (1u << 0) | /* EL1PCTEN, trap phys cnt access. */
			   (1u << 1);  /* EL1PCEN, trap phys timer access. */
	}

	__asm__ volatile("msr hcr_el2, %0" ::"r"(hcr));
	__asm__ volatile("msr cptr_el2, %0" ::"r"(cptr));
	__asm__ volatile("msr cnthctl_el2, %0" ::"r"(cnthctl));
}

static inline void arch_regs_init(struct arch_regs *r, ipaddr_t pc, size_t arg)
{
	/* TODO: Use constant here. */
	r->spsr = 5 |	 /* M bits, set to EL1h. */
		  (0xf << 6); /* DAIF bits set; disable interrupts. */
	r->pc = ipa_addr(pc);
	r->r[0] = arg;
}

static inline void arch_regs_set_retval(struct arch_regs *r, size_t v)
{
	r->r[0] = v;
}
