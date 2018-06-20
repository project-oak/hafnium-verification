#include <stdint.h>

#include "cpu.h"
#include "irq.h"
#include "msr.h"

static bool timer_irq_handler(void *context, struct irq_handle *h)
{
	struct cpu *c = cpu();

	/* Mask timer interrupt and dismiss current interrupt. */
	write_msr(cnthp_ctl_el2, read_msr(cnthp_ctl_el2) | 0x2);
	irq_dismiss(h);

	/* Execute user-supplied callback. */
	if (c->timer_cb)
		return c->timer_cb(c->timer_context);

	return false;
}

void timer_set(uint64_t time, bool (*cb)(void *), void *context)
{
	uint64_t v;
	struct cpu *c = cpu();

	/* Save callback. */
	c->timer_cb = cb;
	c->timer_context = context;

	/* TODO: There's a better way to advance this. */
	v = read_msr(cntpct_el0);
	write_msr(CNTHP_CVAL_EL2, v + time);
	write_msr(cnthp_ctl_el2, 1); /* enable. */
}

void timer_init(void)
{
	irq_config(TIMER_IRQ, irq_trigger_level, irq_polarity_active_high,
		   timer_irq_handler, NULL);
}

void timer_init_percpu(void)
{
	/* Mask timer interrupt for now. */
	write_msr(cnthp_ctl_el2, read_msr(cnthp_ctl_el2) | 0x2);

	irq_enable(TIMER_IRQ);
}
