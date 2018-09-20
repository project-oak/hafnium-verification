#include "hf/cpu.h"

#include <stdalign.h>

#include "hf/arch/cpu.h"

#include "hf/api.h"
#include "hf/dlog.h"
#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

/* The stack to be used by the CPUs. */
alignas(2 * sizeof(size_t)) static char callstacks[MAX_CPUS][STACK_SIZE];

/* State of all supported CPUs. The stack of the first one is initialized. */
struct cpu cpus[MAX_CPUS] = {
	{
		.is_on = 1,
		.stack_bottom = &callstacks[0][STACK_SIZE],
	},
};

void cpu_module_init(void)
{
	size_t i;

	/* Initialize all CPUs. */
	for (i = 0; i < MAX_CPUS; i++) {
		struct cpu *c = &cpus[i];
		cpu_init(c);
		c->id = i; /* TODO: Initialize ID based on fdt. */
		c->stack_bottom = &callstacks[i][STACK_SIZE];
	}
}

size_t cpu_index(struct cpu *c)
{
	return c - cpus;
}

void cpu_init(struct cpu *c)
{
	/* TODO: Assumes that c is zeroed out already. */
	sl_init(&c->lock);
	c->irq_disable_count = 1;
}

void cpu_irq_enable(struct cpu *c)
{
	c->irq_disable_count--;
	if (!c->irq_disable_count) {
		arch_irq_enable();
	}
}

void cpu_irq_disable(struct cpu *c)
{
	if (!c->irq_disable_count) {
		arch_irq_disable();
	}
	c->irq_disable_count++;
}

/**
 * Turns CPU on and returns the previous state.
 */
bool cpu_on(struct cpu *c, ipaddr_t entry, size_t arg)
{
	bool prev;

	sl_lock(&c->lock);
	prev = c->is_on;
	c->is_on = true;
	sl_unlock(&c->lock);

	if (!prev) {
		struct vcpu *vcpu =
			&vm_get(HF_PRIMARY_VM_ID)->vcpus[cpu_index(c)];
		arch_regs_init(&vcpu->regs, entry, arg);
		vcpu_on(vcpu);
	}

	return prev;
}

/**
 * Prepares the CPU for turning itself off.
 */
void cpu_off(struct cpu *c)
{
	sl_lock(&c->lock);
	c->is_on = false;
	sl_unlock(&c->lock);
}

/**
 * Searches for a CPU based on its id.
 */
struct cpu *cpu_find(size_t id)
{
	size_t i;

	for (i = 0; i < MAX_CPUS; i++) {
		if (cpus[i].id == id) {
			return &cpus[i];
		}
	}

	return NULL;
}

void vcpu_init(struct vcpu *vcpu, struct vm *vm)
{
	memset(vcpu, 0, sizeof(*vcpu));
	sl_init(&vcpu->lock);
	vcpu->vm = vm;
	vcpu->state = vcpu_state_off;
	/* TODO: This needs to be moved to arch-dependent code. */
	vcpu->regs.lazy.vmpidr_el2 = vcpu - vm->vcpus;
}

void vcpu_on(struct vcpu *vcpu)
{
	sl_lock(&vcpu->lock);
	vcpu->state = vcpu_state_ready;
	sl_unlock(&vcpu->lock);
}

void vcpu_off(struct vcpu *vcpu)
{
	sl_lock(&vcpu->lock);
	vcpu->state = vcpu_state_off;
	sl_unlock(&vcpu->lock);
}
