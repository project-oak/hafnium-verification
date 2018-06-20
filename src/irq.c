#include "irq.h"

#include "arch.h"

struct irq_config {
	void *cb_context;
	bool (*cb)(void *context, struct irq_handle *);
};

/*
 * TODO: Move this to write-once page so that we know it won't change in the
 * future.
 */
static struct irq_config irq_configs[300];

void irq_config(uint32_t num, enum irq_trigger t, enum irq_polarity p,
		bool (*cb)(void *, struct irq_handle *), void *context)
{
	struct irq_config *cfg = irq_configs + num;

	cfg->cb = cb;
	cfg->cb_context = context;

	arch_irq_config(num, t, p);
}

bool irq_handle(uint32_t num, struct irq_handle *h)
{
	struct irq_config *cfg = irq_configs + num;

	return cfg->cb(cfg->cb_context, h);
}

void irq_init(void)
{
}

void irq_init_percpu(void)
{
	arch_irq_init_percpu();
}
