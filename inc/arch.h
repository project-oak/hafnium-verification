#ifndef _ARCH_H
#define _ARCH_H

#include "cpu.h"
#include "irq.h"

void arch_init(struct cpu *cpu);
void arch_irq_init_percpu(void);
void arch_irq_config(uint32_t num, enum irq_trigger t, enum irq_polarity p);
void arch_putchar(char c);

#endif  /* _ARCH_H */
