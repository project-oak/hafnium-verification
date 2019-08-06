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

#include "hf/mm.h"

#include "hf/arch/barriers.h"

#include "hf/dlog.h"

#include "../msr.h"

#define STAGE1_DEVICEINDX UINT64_C(0)
#define STAGE1_NORMALINDX UINT64_C(1)

/**
 * Initialize MMU for a test running in EL1.
 */
bool arch_vm_mm_init(paddr_t table)
{
	static const int pa_bits_table[16] = {32, 36, 40, 42, 44, 48};
	uint64_t features = read_msr(id_aa64mmfr0_el1);
	uint64_t v;
	int pa_bits = pa_bits_table[features & 0xf];

	/* Check that 4KB granules are supported. */
	if ((features >> 28) & 0xf) {
		dlog("4KB granules are not supported\n");
		return false;
	}

	/* Check the physical address range. */
	if (!pa_bits) {
		dlog("Unsupported value of id_aa64mmfr0_el1.PARange: %x\n",
		     features & 0xf);
		return false;
	}

	/*
	 * 0    -> Device-nGnRnE memory
	 * 0xff -> Normal memory, Inner/Outer Write-Back Non-transient,
	 *         Write-Alloc, Read-Alloc.
	 */
	v = (0 << (8 * STAGE1_DEVICEINDX)) | (0xff << (8 * STAGE1_NORMALINDX));
	write_msr(mair_el1, v);

	write_msr(ttbr0_el1, pa_addr(table));

	v = (1 << 20) |		       /* TBI, top byte ignored. */
	    ((features & 0xf) << 16) | /* PS. */
	    (0 << 14) |		       /* TG0, granule size, 4KB. */
	    (3 << 12) |		       /* SH0, inner shareable. */
	    (1 << 10) | /* ORGN0, normal mem, WB RA WA Cacheable. */
	    (1 << 8) |  /* IRGN0, normal mem, WB RA WA Cacheable. */
	    (25 << 0) | /* T0SZ, input address is 2^39 bytes. */
	    0;
	write_msr(tcr_el1, v);

	v = (1 << 0) |  /* M, enable stage 1 EL2 MMU. */
	    (1 << 1) |  /* A, enable alignment check faults. */
	    (1 << 2) |  /* C, data cache enable. */
	    (1 << 3) |  /* SA, enable stack alignment check. */
	    (3 << 4) |  /* RES1 bits. */
	    (1 << 11) | /* RES1 bit. */
	    (1 << 12) | /* I, instruction cache enable. */
	    (1 << 16) | /* RES1 bit. */
	    (1 << 18) | /* RES1 bit. */
	    (0 << 19) | /* WXN bit, writable execute never. */
	    (3 << 22) | /* RES1 bits. */
	    (3 << 28) | /* RES1 bits. */
	    0;

	dsb(sy);
	isb();
	write_msr(sctlr_el1, v);
	isb();

	return true;
}
