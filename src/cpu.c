#include "cpu.h"

#include "arch_cpu.h"
#include "dlog.h"
#include "std.h"
#include "vm.h"

void cpu_init(struct cpu *c)
{
	/* TODO: Assumes that c is zeroed out already. */
	sl_init(&c->lock);
	c->irq_disable_count = 1;
}

void cpu_irq_enable(struct cpu *c)
{
	c->irq_disable_count--;
	if (!c->irq_disable_count)
		arch_irq_enable();
}

void cpu_irq_disable(struct cpu *c)
{
	if (!c->irq_disable_count)
		arch_irq_disable();
	c->irq_disable_count++;
}

/**
 * Turns CPU on and returns the previous state.
 */
bool cpu_on(struct cpu *c)
{
	bool prev;

	sl_lock(&c->lock);
	prev = c->is_on;
	c->is_on = true;
	sl_unlock(&c->lock);

	if (!prev) {
		/* The CPU is currently off, we need to turn it on. */
		arch_cpu_on(c->id, c);
	}

	return prev;
}

/*
 * This must be called only from the same CPU.
 */
void cpu_off(struct cpu *c)
{
	sl_lock(&c->lock);
	c->is_on = false;
	sl_unlock(&c->lock);

	arch_cpu_off();
}

void vcpu_init(struct vcpu *vcpu, struct vm *vm)
{
	memset(vcpu, 0, sizeof(*vcpu));
	sl_init(&vcpu->lock);
	vcpu->vm = vm;
	/* TODO: Initialize vmid register. */
}

void vcpu_on(struct vcpu *vcpu)
{
	sl_lock(&vcpu->lock);
	vcpu->is_on = true;
	sl_unlock(&vcpu->lock);
}

void vcpu_off(struct vcpu *vcpu)
{
	sl_lock(&vcpu->lock);
	vcpu->is_on = false;
	sl_unlock(&vcpu->lock);
}
