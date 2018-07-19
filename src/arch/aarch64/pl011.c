#include "dlog.h"
#include "io.h"

/* UART Data Register. */
#define UARTDR 0

/* UART Flag Register. */
#define UARTFR 0x018

/* UART Flag Register bit: transmit fifo is full. */
#define UARTFR_TXFF (1 << 5)

/* UART Flag Register bit: UART is busy. */
#define UARTFR_BUSY (1 << 3)

void arch_putchar(char c)
{
	/* Print a carriage-return as well. */
	if (c == '\n')
		arch_putchar('\r');

	/* Wait until there is room in the tx buffer. */
	while (io_read(PL011_BASE + UARTFR) & UARTFR_TXFF)
		;

	dmb();

	/* Write the character out. */
	io_write(PL011_BASE + UARTDR, c);

	dmb();

	/* Wait until the UART is no longer busy. */
	while (io_read_mb(PL011_BASE + UARTFR) & UARTFR_BUSY)
		;
}
