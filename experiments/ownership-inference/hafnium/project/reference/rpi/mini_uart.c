/*
 * Copyright 2019 The Hafnium Authors.
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

#include "hf/io.h"
#include "hf/mm.h"
#include "hf/mpool.h"
#include "hf/plat/console.h"

/* clang-format off */

#define GPFSEL1               IO32_C(GPIO_BASE + 0x4)

#define AUX_ENABLES           IO32_C(AUX_BASE + 0x4)
#define AUX_MU_IO_REG         IO32_C(AUX_BASE + 0x40)
#define AUX_MU_IER_REG        IO32_C(AUX_BASE + 0x44)
#define AUX_MU_LCR_REG        IO32_C(AUX_BASE + 0x4c)
#define AUX_MU_MCR_REG        IO32_C(AUX_BASE + 0x50)
#define AUX_MU_LSR_REG        IO32_C(AUX_BASE + 0x54)
#define AUX_MU_CNTL_REG       IO32_C(AUX_BASE + 0x60)
#define AUX_MU_BAUD_REG       IO32_C(AUX_BASE + 0x68)

#define AUX_MU_LSR_TX_EMPTY   (UINT32_C(1) << 5)
#define AUX_MU_LSR_TX_IDLE    (UINT32_C(1) << 6)

#define MHZ_TO_HZ             UINT32_C(1000000)

/* clang-format on */

void plat_console_init(void)
{
	uint32_t selector;

	selector = io_read32(GPFSEL1);
	/* Set GPIO14 to function 5. */
	selector &= ~(7 << 12);
	selector |= 2 << 12;
	/* Set GPIO15 to function 5 */
	selector &= ~(7 << 15);
	selector |= 2 << 15;
	io_write32(GPFSEL1, selector);

	/*
	 * With 8-times oversampling, baudrate is calculated as:
	 *   baudrate = system_clock_freq / (8 * (baudrate_reg + 1))
	 * Therefore:
	 *   baudrate_reg = (system_clock_freq / (8 * baudrate)) -1
	 */
	uint32_t system_clock_freq = UINT32_C(CORE_FREQ_MHZ) * MHZ_TO_HZ;
	uint32_t oversampled_baudrate = UINT32_C(8) * UINT32_C(BAUDRATE);
	uint32_t baudrate_reg =
		(system_clock_freq / oversampled_baudrate) - UINT32_C(1);

	/* Enable Mini UART and access to its registers. */
	io_write32(AUX_ENABLES, 1);
	/* Disable auto flow control and disable receiver and transmitter. */
	io_write32(AUX_MU_CNTL_REG, 0);
	/* Disable receive and transmit interrupts. */
	io_write32(AUX_MU_IER_REG, 0);
	/* Enable 8 bit mode. */
	io_write32(AUX_MU_LCR_REG, 3);
	/* Set RTS line to be always high. */
	io_write32(AUX_MU_MCR_REG, 0);
	/* Set baud rate. */
	io_write32(AUX_MU_BAUD_REG, baudrate_reg);
	/* Enable transmitter and receiver. */
	io_write32(AUX_MU_CNTL_REG, 3);

	memory_ordering_barrier();
}

void plat_console_mm_init(struct mm_stage1_locked stage1_locked,
			  struct mpool *ppool)
{
	mm_identity_map(stage1_locked, pa_init(GPIO_BASE),
			pa_add(pa_init(GPIO_BASE), PAGE_SIZE),
			MM_MODE_R | MM_MODE_W | MM_MODE_D, ppool);
	mm_identity_map(stage1_locked, pa_init(AUX_BASE),
			pa_add(pa_init(AUX_BASE), PAGE_SIZE),
			MM_MODE_R | MM_MODE_W | MM_MODE_D, ppool);
}

void plat_console_putchar(char c)
{
	/* Print a carriage-return as well. */
	if (c == '\n') {
		plat_console_putchar('\r');
	}

	/* Wait for the transmitter to be ready to accept a byte. */
	while ((io_read32(AUX_MU_LSR_REG) & AUX_MU_LSR_TX_EMPTY) == 0) {
	}

	/* Write data to transmitter FIFO. */
	memory_ordering_barrier();
	io_write32(AUX_MU_IO_REG, c);
	memory_ordering_barrier();

	/* Wait until the transmitter is no longer busy. */
	while ((io_read32(AUX_MU_LSR_REG) & AUX_MU_LSR_TX_IDLE) == 0) {
	}
}
