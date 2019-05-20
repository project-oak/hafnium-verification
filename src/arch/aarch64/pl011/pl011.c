/*
 * Copyright 2018 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "hf/mm.h"
#include "hf/mpool.h"
#include "hf/plat/console.h"
#include "hf/vm.h"

#include "io.h"

/* UART Data Register. */
#define UARTDR 0

/* UART Flag Register. */
#define UARTFR 0x018

/* UART Flag Register bit: transmit fifo is full. */
#define UARTFR_TXFF (1 << 5)

/* UART Flag Register bit: UART is busy. */
#define UARTFR_BUSY (1 << 3)

void plat_console_init(void)
{
	/* No hardware initialisation required. */
}

void plat_console_mm_init(struct mpool *ppool)
{
	/* Map page for UART. */
	mm_identity_map(pa_init(PL011_BASE),
			pa_add(pa_init(PL011_BASE), PAGE_SIZE),
			MM_MODE_R | MM_MODE_W | MM_MODE_D, ppool);
}

/* TODO: Remove this. */
void plat_console_vm_mm_init(struct vm *vm, struct mpool *ppool)
{
	/* Grant VM access to UART. */
	mm_vm_identity_map(&vm->ptable, pa_init(PL011_BASE),
			   pa_add(pa_init(PL011_BASE), PAGE_SIZE),
			   MM_MODE_R | MM_MODE_W, NULL, ppool);
}

void plat_console_putchar(char c)
{
	/* Print a carriage-return as well. */
	if (c == '\n') {
		plat_console_putchar('\r');
	}

	/* Wait until there is room in the tx buffer. */
	while (io_read(PL011_BASE + UARTFR) & UARTFR_TXFF) {
		/* do nothing */
	}

	dmb();

	/* Write the character out. */
	io_write(PL011_BASE + UARTDR, c);

	dmb();

	/* Wait until the UART is no longer busy. */
	while (io_read_mb(PL011_BASE + UARTFR) & UARTFR_BUSY) {
		/* do nothing */
	}
}
