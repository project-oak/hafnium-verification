/*
 * Copyright 2018 Google LLC
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

#include "hf/arch/cpu.h"

#include "hf/dlog.h"

#include "msr.h"

/* Keep macro alignment */
/* clang-format off */

#define NON_SHAREABLE   UINT64_C(0)
#define OUTER_SHAREABLE UINT64_C(2)
#define INNER_SHAREABLE UINT64_C(3)

#define STAGE1_XN          (UINT64_C(1) << 54)
#define STAGE1_PXN         (UINT64_C(1) << 53)
#define STAGE1_CONTIGUOUS  (UINT64_C(1) << 52)
#define STAGE1_DBM         (UINT64_C(1) << 51)
#define STAGE1_NG          (UINT64_C(1) << 11)
#define STAGE1_AF          (UINT64_C(1) << 10)
#define STAGE1_SH(x)       ((x) << 8)
#define STAGE1_AP2         (UINT64_C(1) << 7)
#define STAGE1_AP1         (UINT64_C(1) << 6)
#define STAGE1_AP(x)       ((x) << 6)
#define STAGE1_NS          (UINT64_C(1) << 5)
#define STAGE1_ATTRINDX(x) ((x) << 2)

#define STAGE1_READONLY  UINT64_C(2)
#define STAGE1_READWRITE UINT64_C(0)

#define STAGE1_DEVICEINDX UINT64_C(0)
#define STAGE1_NORMALINDX UINT64_C(1)

#define STAGE2_XN(x)      ((x) << 53)
#define STAGE2_CONTIGUOUS (UINT64_C(1) << 52)
#define STAGE2_DBM        (UINT64_C(1) << 51)
#define STAGE2_AF         (UINT64_C(1) << 10)
#define STAGE2_SH(x)      ((x) << 8)
#define STAGE2_S2AP(x)    ((x) << 6)
#define STAGE2_MEMATTR(x) ((x) << 2)

#define STAGE2_EXECUTE_ALL  UINT64_C(0)
#define STAGE2_EXECUTE_EL0  UINT64_C(1)
#define STAGE2_EXECUTE_NONE UINT64_C(2)
#define STAGE2_EXECUTE_EL1  UINT64_C(3)

/* Table attributes only apply to stage 1 translations. */
#define TABLE_NSTABLE  (UINT64_C(1) << 63)
#define TABLE_APTABLE1 (UINT64_C(1) << 62)
#define TABLE_APTABLE0 (UINT64_C(1) << 61)
#define TABLE_XNTABLE  (UINT64_C(1) << 60)
#define TABLE_PXNTABLE (UINT64_C(1) << 59)

/* The following are stage-2 memory attributes for normal memory. */
#define STAGE2_NONCACHEABLE UINT64_C(1)
#define STAGE2_WRITETHROUGH UINT64_C(2)
#define STAGE2_WRITEBACK    UINT64_C(3)

#define STAGE2_MEMATTR_NORMAL(outer, inner) ((((outer) << 2) | (inner)) << 2)

/* The following stage-2 memory attributes for device memory. */
#define STAGE2_MEMATTR_DEVICE_nGnRnE (UINT64_C(0) << 2)
#define STAGE2_MEMATTR_DEVICE_nGnRE  (UINT64_C(1) << 2)
#define STAGE2_MEMATTR_DEVICE_nGRE   (UINT64_C(2) << 2)
#define STAGE2_MEMATTR_DEVICE_GRE    (UINT64_C(3) << 2)

#define STAGE2_ACCESS_READ  UINT64_C(1)
#define STAGE2_ACCESS_WRITE UINT64_C(2)

/* clang-format on */

static uint8_t mm_max_s2_level = 2;

uint64_t arch_mm_mode_to_attrs(int mode)
{
	uint64_t attrs = 0;

	if (mode & MM_MODE_STAGE1) {
		attrs |= STAGE1_AF | STAGE1_SH(OUTER_SHAREABLE);

		/* Define the execute bits. */
		if (!(mode & MM_MODE_X)) {
			attrs |= STAGE1_XN;
		}

		/* Define the read/write bits. */
		if (mode & MM_MODE_W) {
			attrs |= STAGE1_AP(STAGE1_READWRITE);
		} else {
			attrs |= STAGE1_AP(STAGE1_READONLY);
		}

		/* Define the memory attribute bits. */
		if (mode & MM_MODE_D) {
			attrs |= STAGE1_ATTRINDX(STAGE1_DEVICEINDX);
		} else {
			attrs |= STAGE1_ATTRINDX(STAGE1_NORMALINDX);
		}
	} else {
		uint64_t access = 0;

		/*
		 * Non-shareable is the "neutral" share mode, i.e., the
		 * shareability attribute of stage 1 will determine the actual
		 * attribute.
		 */
		attrs |= STAGE2_AF | STAGE2_SH(NON_SHAREABLE);

		/* Define the read/write bits. */
		if (mode & MM_MODE_R) {
			access |= STAGE2_ACCESS_READ;
		}

		if (mode & MM_MODE_W) {
			access |= STAGE2_ACCESS_WRITE;
		}

		attrs |= STAGE2_S2AP(access);

		/* Define the execute bits. */
		if (mode & MM_MODE_X) {
			attrs |= STAGE2_XN(STAGE2_EXECUTE_ALL);
		} else {
			attrs |= STAGE2_XN(STAGE2_EXECUTE_NONE);
		}

		/*
		 * Define the memory attribute bits, using the "neutral" values
		 * for either device or normal memory.
		 */
		if (mode & MM_MODE_D) {
			attrs |= STAGE2_MEMATTR_DEVICE_GRE;
		} else {
			attrs |= STAGE2_MEMATTR_NORMAL(STAGE2_WRITEBACK,
						       STAGE2_WRITEBACK);
		}
	}

	return attrs;
}

/**
 * Determines the maximum level supported by the given mode.
 */
uint8_t arch_mm_max_level(int mode)
{
	if (mode & MM_MODE_STAGE1) {
		/*
		 * For stage 1 we hard-code this to 2 for now so that we can
		 * save one page table level at the expense of limiting the
		 * physical memory to 512GB.
		 */
		return 2;
	}

	return mm_max_s2_level;
}

bool arch_mm_init(paddr_t table, bool first)
{
	static const int pa_bits_table[16] = {32, 36, 40, 42, 44, 48};
	uint64_t features = read_msr(id_aa64mmfr0_el1);
	uint64_t v;
	int pa_bits = pa_bits_table[features & 0xf];
	int sl0;

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

	if (first) {
		dlog("Supported bits in physical address: %d\n", pa_bits);
	}

	/*
	 * Determine sl0 based on the number of bits. The maximum value is given
	 * in D4-7 of the ARM arm.
	 */
	if (pa_bits >= 44) {
		mm_max_s2_level = 3;
		sl0 = 2;
	} else {
		mm_max_s2_level = 2;
		sl0 = 1;
	}

	if (first) {
		dlog("Number of page table levels: %d\n", mm_max_s2_level + 1);
	}

	v = (1u << 31) |	       /* RES1. */
	    ((features & 0xf) << 16) | /* PS, matching features. */
	    (0 << 14) |		       /* TG0: 4 KB granule. */
	    (3 << 12) |		       /* SH0: inner shareable. */
	    (1 << 10) |		       /* ORGN0: normal, cacheable ... */
	    (1 << 8) |		       /* IRGN0: normal, cacheable ... */
	    (sl0 << 6) |	       /* SL0. */
	    ((64 - pa_bits) << 0);     /* T0SZ: dependent on PS. */
	write_msr(vtcr_el2, v);

	/*
	 * 0    -> Device-nGnRnE memory
	 * 0xff -> Normal memory, Inner/Outer Write-Back Non-transient,
	 *         Write-Alloc, Read-Alloc.
	 */
	write_msr(mair_el2, (0 << (8 * STAGE1_DEVICEINDX)) |
				    (0xff << (8 * STAGE1_NORMALINDX)));

	write_msr(ttbr0_el2, pa_addr(table));

	/*
	 * Configure tcr_el2.
	 */
	v = (1 << 20) |		       /* TBI, top byte ignored. */
	    ((features & 0xf) << 16) | /* PS. */
	    (0 << 14) |		       /* TG0, granule size, 4KB. */
	    (3 << 12) |		       /* SH0, inner shareable. */
	    (1 << 10) | /* ORGN0, normal mem, WB RA WA Cacheable. */
	    (1 << 8) |  /* IRGN0, normal mem, WB RA WA Cacheable. */
	    (25 << 0) | /* T0SZ, input address is 2^39 bytes. */
	    0;
	write_msr(tcr_el2, v);

	v = (1 << 0) |  /* M, enable stage 1 EL2 MMU. */
	    (1 << 1) |  /* A, enable alignment check faults. */
	    (1 << 2) |  /* C, data cache enable. */
	    (1 << 3) |  /* SA, enable stack alignment check. */
	    (3 << 4) |  /* RES1 bits. */
	    (1 << 11) | /* RES1 bit. */
	    (1 << 12) | /* I, instruction cache enable. */
	    (1 << 16) | /* RES1 bit. */
	    (1 << 18) | /* RES1 bit. */
	    (1 << 19) | /* WXN bit, writable execute never. */
	    (3 << 22) | /* RES1 bits. */
	    (3 << 28) | /* RES1 bits. */
	    0;

	__asm__ volatile("dsb sy");
	__asm__ volatile("isb");
	write_msr(sctlr_el2, v);
	__asm__ volatile("isb");

	return true;
}

uint64_t arch_mm_combine_table_entry_attrs(uint64_t table_attrs,
					   uint64_t block_attrs)
{
	/*
	 * Only stage 1 table descriptors have attributes, but the bits are res0
	 * for stage 2 table descriptors so this code is safe for both.
	 */
	if (table_attrs & TABLE_NSTABLE) {
		block_attrs |= STAGE1_NS;
	}
	if (table_attrs & TABLE_APTABLE1) {
		block_attrs |= STAGE1_AP2;
	}
	if (table_attrs & TABLE_APTABLE0) {
		block_attrs &= ~STAGE1_AP1;
	}
	if (table_attrs & TABLE_XNTABLE) {
		block_attrs |= STAGE1_XN;
	}
	if (table_attrs & TABLE_PXNTABLE) {
		block_attrs |= STAGE1_PXN;
	}
	return block_attrs;
}
