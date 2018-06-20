#include "dlog.h"
#include "io.h"
#include "irq.h"

#define GICD_CTLR       (0x00)
#define GICD_TYPER      (0x04)
#define GICD_ISENABLER  (0x100)
#define GICD_ICENABLER  (0x180)
#define GICD_ICPENDR    (0x280)
#define GICD_ICACTIVER  (0x380)
#define GICD_IPRIORITYR (0x400)
#define GICD_ITARGETSR  (0x800)
#define GICD_ICFGR      (0xc00)

#define GICC_CTLR (0x000)
#define GICC_PMR  (0x004)
#define GICC_IAR  (0x00c)
#define GICC_EOIR (0x010)

struct irq_handle {
	uint32_t iar;
};

/*
 * Dismisses an irq that was signaled and is being processed.
 */
void irq_dismiss(struct irq_handle *h)
{
	io_write(GICC_BASE + GICC_EOIR, h->iar);
}

/*
 * Configures the given irq number before it can be enabled.
 */
void arch_irq_config(uint32_t num, enum irq_trigger t, enum irq_polarity p)
{
	uint32_t v = io_read(GICD_BASE + GICD_ICFGR + (num / 16) * 4);

	if (t == irq_trigger_level)
		v &= ~(2u << ((num % 16) * 2));
	else
		v |= 2u << ((num % 16) * 2);

	io_write(GICD_BASE + GICD_ICFGR + (num / 16) * 4, v);
}

/*
 * Enables the given irq number such that interrupts will be signaled when its
 * interrupt line is asserted. A caller must first configure the irq before
 * enabling it.
 */
void irq_enable(uint32_t num)
{
	io_write(GICD_BASE + GICD_ISENABLER + (num / 32) * 4,
		 (1u << (num % 32)));
}

/*
 * Handles an interrupt signaled when the CPU was in a lower level (EL0 or EL1),
 * it is called directly from the exception handler.
 *
 * The return value indicates whether a new vcpu should be scheduled.
 */
bool irq_handle_lower(void)
{
	struct irq_handle h = {
		.iar = io_read(GICC_BASE + GICC_IAR),
	};

	dlog("irq: %u\n", h.iar & 0x3ff);

	return irq_handle(h.iar & 0x3ff, &h);
}

/*
 * Initializes the GICv2 for use as the interrupt controller.
 */
void arch_irq_init_percpu(void)
{
	uint32_t i;
	uint32_t max = 32 * (1 + (io_read(GICD_BASE + GICD_TYPER) & 0x1f));

	/* Disable all irqs, clear pending & active states. */
	for (i = 0; i < (max + 31) / 32; i++) {
		io_write(GICD_BASE + GICD_ICENABLER + i * 4, 0xffffffff);
		io_write(GICD_BASE + GICD_ICACTIVER + i * 4, 0xffffffff);
		io_write(GICD_BASE + GICD_ICPENDR + i * 4, 0xffffffff);
	}

	/* Set the priority to zero, and cpu target to cpu 0 by default. */
	for (i = 0; i < (max + 3) / 4; i++) {
		io_write(GICD_BASE + GICD_IPRIORITYR + i * 4, 0);
		io_write(GICD_BASE + GICD_ITARGETSR + i * 4, 0x01010101);
	}

	/* Allow all irq levels to interrupt the current CPU. */
	io_write(GICC_BASE + GICC_PMR, 0xff);

	/* Enable distributor and CPU interfaces. */
	io_write(GICD_BASE + GICD_CTLR, 1);
	io_write(GICC_BASE + GICC_CTLR, 1);
}
