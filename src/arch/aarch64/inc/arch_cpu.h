#ifndef _ARCH_CPU_H
#define _ARCH_CPU_H

#include <stdalign.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct arch_regs {
	/* General purpose registers. */
	uint64_t r[31];
	uint64_t pc;
	uint64_t spsr;

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
		uint64_t hcr_el2;
	} lazy;
};

struct arch_page_table {
	alignas(4096) uint64_t first[512];
	alignas(4096) uint64_t entry0[512];
	alignas(4096) uint64_t entry1[512];
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

static inline
void arch_regs_init(struct arch_regs *r, size_t pc, size_t arg, bool is_primary)
{
	/* TODO: Use constant here. */
	r->spsr = 5 |         /* M bits, set to EL1h. */
		  (0xf << 6); /* DAIF bits set; disable interrupts. */
	r->pc = pc;
	r->r[0] = arg;
	r->lazy.hcr_el2 = (1u << 31) |  /* RW bit. */
			  (1u << 2) |   /* PTW, Protected Table Walk. */
			  (1u << 0);    /* VM: enable stage-2 translation. */

	if (!is_primary)
		r->lazy.hcr_el2 |= (7u << 3) |   /* AMO, IMO, FMO bits. */
				   (3u << 13);   /* TWI, TWE bits. */
}

static inline void arch_regs_set_retval(struct arch_regs *r, size_t v)
{
	r->r[0] = v;
}

static inline void arch_regs_set_irq(struct arch_regs *r)
{
	/* Set the VI bit. */
	r->lazy.hcr_el2 |= (1u << 7);
}

static inline void arch_regs_clear_irq(struct arch_regs *r)
{
	/* Clear the VI bit. */
	r->lazy.hcr_el2 &= ~(1u << 7);
}

/* TODO: Figure out what to do with this. */
int32_t smc(size_t arg0, size_t arg1, size_t arg2, size_t arg3);

static inline void arch_cpu_on(size_t id, void *ctx)
{
	void cpu_entry(void *ctx);
	int32_t ret;

	/*
	 * There's a race when turning a CPU on when it's in the process of
	 * turning off. We need to loop here while it is reported that the CPU
	 * is on (because it's about to turn itself off).
	 */
	do {
		/* CPU_ON */
		ret = smc(0xC4000003, id, (size_t)&cpu_entry, (size_t)ctx);
	} while (ret == -4); /* ALREADY_ON */
}

static inline void arch_cpu_off(void)
{
	/* CPU_OFF */
	smc(0xC4000002, 0, 0, 0);
}

static inline void arch_set_vm_mm(struct arch_page_table *table)
{
	__asm volatile("msr vttbr_el2, %0" : : "r" ((size_t)table));
}

void arch_vptable_init(struct arch_page_table *table);

#endif  /* _ARCH_CPU_H */
