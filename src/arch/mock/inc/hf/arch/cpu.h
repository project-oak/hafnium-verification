#pragma once

#include <stdint.h>

struct arch_regs {
	uint32_t r[5];
};

static inline struct cpu *cpu(void)
{
	/* TODO: */
	return NULL;
}

static inline void arch_irq_disable(void)
{
	/* TODO */
}

static inline void arch_irq_enable(void)
{
	/* TODO */
}
