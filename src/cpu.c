#include "cpu.h"

#include "arch_cpu.h"
#include "dlog.h"
#include "std.h"
#include "timer.h"
#include "vm.h"

struct new_old_vcpu {
	struct vcpu *new;
	struct vcpu *old;
};

void cpu_init(struct cpu *c)
{
	/* TODO: Assumes that c is zeroed out already. */
	sl_init(&c->lock);
	list_init(&c->ready_queue);
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

void cpu_on(struct cpu *c)
{
	sl_lock(&c->lock);
	if (!c->cpu_on_count) {
		/* The CPU is currently off, we need to turn it on. */
		arch_cpu_on(c->id, c);
	}
	c->cpu_on_count++;
	sl_unlock(&c->lock);
}

/*
 * This must be called only from the same CPU.
 */
void cpu_off(struct cpu *c)
{
	bool on;

	sl_lock(&c->lock);
	c->cpu_on_count--;
	on = c->cpu_on_count > 0;
	sl_unlock(&c->lock);

	if (!on)
		arch_cpu_off();
}

void vcpu_ready(struct vcpu *v)
{
	struct cpu *c = v->cpu;

	sl_lock(&c->lock);
	if (!v->is_runnable) {
		v->is_runnable = true;
		list_append(&c->ready_queue, &v->links);
		/* TODO: Send IPI to cpu if needed. */
	}
	sl_unlock(&c->lock);
}

void vcpu_unready(struct vcpu *v)
{
	struct cpu *c = v->cpu;

	sl_lock(&c->lock);
	if (v->is_runnable) {
		v->is_runnable = false;
		list_remove(&v->links);
	}
	sl_unlock(&c->lock);
}

#if 0
static bool cpu_schedule_next(void *ctx)
{
	/* Indicate that a new vcpu should be chosen. */
	return true;
}
#endif

struct new_old_vcpu cpu_next_vcpu(void)
{
	struct cpu *c = cpu();
	struct new_old_vcpu ret;
	struct vcpu *next;
	bool switch_mm;

	/* TODO: Check if too soon. */

	sl_lock(&c->lock);

	ret.old = c->current;
	if (list_empty(&c->ready_queue)) {
		bool first = true;
		c->current = NULL;
		do {
			sl_unlock(&c->lock);
			/* TODO: Implement this. Enable irqs. */
			if (first) {
				dlog("CPU%d waiting for work...\n", c->id);
				first = false;
			}
			sl_lock(&c->lock);
		} while (list_empty(&c->ready_queue));
		dlog("CPU%d found work!\n", c->id);
	}

	next = LIST_ELEM(c->ready_queue.next, struct vcpu, links);
	if (next->links.next != &c->ready_queue) {
		/* Move new vcpu to the end of ready queue. */
		list_remove(&next->links);
		list_append(&c->ready_queue, &next->links);
	}

	c->current = next;

	if (next->interrupt) {
		arch_regs_set_irq(&next->regs);
		next->interrupt = false;
	} else {
		arch_regs_clear_irq(&next->regs);
	}

	switch_mm = !ret.old || ret.old->vm != next->vm;

	sl_unlock(&c->lock);

	ret.new = next;

	if (switch_mm)
		arch_set_vm_mm(&next->vm->page_table);

	/* TODO: Only set this when there is a next thing to run. */
	/* Set timer again. */
	//timer_set(5 * 1000000, cpu_schedule_next, NULL);

	return ret;
}

void vcpu_init(struct vcpu *vcpu, struct cpu *cpu, struct vm *vm)
{
	memset(vcpu, 0, sizeof(*vcpu));
	vcpu->cpu = cpu;
	vcpu->vm = vm;
	/* TODO: Initialize vmid register. */
}
