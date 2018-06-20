#ifndef _CPU_H
#define _CPU_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "arch_cpu.h"
#include "list.h"
#include "spinlock.h"

struct vcpu {
	struct list_entry links;
	bool is_runnable;
	bool interrupt;
	struct arch_regs regs;
	struct cpu *cpu;
	struct vm *vm;
};

/* TODO: Update alignment such that cpus are in different cache lines. */
struct cpu {
	struct spinlock lock;

	struct vcpu *current;

	struct list_entry ready_queue;

	/*
	 * Enabling/disabling irqs are counted per-cpu. They are enabled when
	 * the count is zero, and disabled when it's non-zero.
	 */
	uint32_t irq_disable_count;

	/*
	 * The number of VMs that have turned this CPU on. CPUs are off when
	 * this count is zero, and on when this count is ono-zero.
	 */
	uint32_t cpu_on_count;

	bool (*timer_cb)(void *context);
	void *timer_context;

	/* CPU identifier. Doesn't have to be contiguous. */
	size_t id;

	/* Pointer to bottom of the stack. */
	void *stack_bottom;
};

void cpu_init(struct cpu *c);
void cpu_irq_enable(struct cpu *c);
void cpu_irq_disable(struct cpu *c);
void cpu_on(struct cpu *c);
void cpu_off(struct cpu *c);

void vcpu_init(struct vcpu *vcpu, struct cpu *cpu, struct vm *vm);
void vcpu_ready(struct vcpu *v);
void vcpu_unready(struct vcpu *v);

#endif  /* _CPU_H */
