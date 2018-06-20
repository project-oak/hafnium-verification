#ifndef _IRQ_H
#define _IRQ_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct irq_handle;

enum irq_trigger {
	irq_trigger_level,
	irq_trigger_edge,
};

enum irq_polarity {
	irq_polarity_active_high,
	irq_polarity_active_low,
};

/* TODO: Add target CPUs here. */
void irq_config(uint32_t num, enum irq_trigger t, enum irq_polarity p,
		bool (*cb)(void *, struct irq_handle *), void *context);
void irq_enable(uint32_t num);

void irq_dismiss(struct irq_handle *h);

/* TODO: These don't really belong here, do they?. */
bool irq_handle(uint32_t num, struct irq_handle *h);
void irq_init(void);
void irq_init_percpu(void);

#endif
