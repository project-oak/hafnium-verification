#include "mm.h"
#include "arch_cpu.h"
#include "msr.h"

/* Keep macro alignment */
/* clang-format off */

#define NON_SHAREABLE   0ull
#define OUTER_SHAREABLE 2ull
#define INNER_SHAREABLE 3ull

#define STAGE1_XN          (1ull << 54)
#define STAGE1_CONTIGUOUS  (1ull << 52)
#define STAGE1_DBM         (1ull << 51)
#define STAGE1_NG          (1ull << 11)
#define STAGE1_AF          (1ull << 10)
#define STAGE1_SH(x)       ((x) << 8)
#define STAGE1_AP(x)       ((x) << 6)
#define STAGE1_NS          (1ull << 5)
#define STAGE1_ATTRINDX(x) ((x) << 2)

#define STAGE1_READONLY  2ull
#define STAGE1_READWRITE 0ull

#define STAGE1_DEVICEINDX 0ull
#define STAGE1_NORMALINDX 1ull

#define STAGE2_XN(x)      ((x) << 53)
#define STAGE2_CONTIGUOUS (1ull << 52)
#define STAGE2_DBM        (1ull << 51)
#define STAGE2_AF         (1ull << 10)
#define STAGE2_SH(x)      ((x) << 8)
#define STAGE2_S2AP(x)    ((x) << 6)
#define STAGE2_MEMATTR(x) ((x) << 2)

#define STAGE2_EXECUTE_ALL  0ull
#define STAGE2_EXECUTE_EL0  1ull
#define STAGE2_EXECUTE_NONE 2ull
#define STAGE2_EXECUTE_EL1  3ull

/* The following are stage-2 memory attributes for normal memory. */
#define STAGE2_NONCACHEABLE 1ull
#define STAGE2_WRITETHROUGH 2ull
#define STAGE2_WRITEBACK    3ull

#define STAGE2_MEMATTR_NORMAL(outer, inner) ((outer << 2) | (inner))

/* The following stage-2 memory attributes for device memory. */
#define STAGE2_MEMATTR_DEVICE_nGnRnE 0ull
#define STAGE2_MEMATTR_DEVICE_nGnRE  1ull
#define STAGE2_MEMATTR_DEVICE_nGRE   2ull
#define STAGE2_MEMATTR_DEVICE_GRE    3ull

#define STAGE2_ACCESS_READ  1ull
#define STAGE2_ACCESS_WRITE 2ull

/* clang-format on */

void arch_vptable_init(struct arch_page_table *table)
{
	uint64_t i;

	/* TODO: Check each bit. */
	for (i = 0; i < 512; i++) {
		table->entry0[i] =
			1 | (i << 30) | /* Address */
			(1 << 10) |     /* Access flag. */
			(0 << 8) |  /* sh: non-shareable. this preserves EL1. */
			(3 << 6) |  /* rw */
			(0xf << 2); /* normal mem; preserves EL0/1. */
		table->entry1[i] =
			1 | ((i + 512) << 30) | /* Address */
			(1 << 10) |		/* Access flag. */
			(0 << 8) |  /* sh: non-shareable. this preserves EL1. */
			(3 << 6) |  /* rw */
			(0xf << 2); /* normal mem; preserves EL0/1. */
		table->first[i] = 0;
	}

	table->first[0] = (uint64_t)&table->entry0[0] | 3;
	table->first[1] = (uint64_t)&table->entry1[0] | 3;
}

uint64_t arch_mm_mode_to_attrs(int mode)
{
	uint64_t attrs = 1; /* Present bit. */

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

		attrs |= STAGE2_AF | STAGE2_SH(OUTER_SHAREABLE);

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

		/* Define the memory attribute bits. */
		if (mode & MM_MODE_D) {
			attrs |= STAGE2_MEMATTR_DEVICE_nGnRnE;
		} else {
			attrs |= STAGE2_MEMATTR_NORMAL(STAGE2_WRITEBACK,
						       STAGE2_WRITEBACK);
		}
	}

	return attrs;
}

void arch_mm_init(paddr_t table)
{
	uint64_t v = (1u << 31) | /* RES1. */
		     (4 << 16) |  /* PS: 44 bits. */
		     (0 << 14) |  /* TG0: 4 KB granule. */
		     (3 << 12) |  /* SH0: inner shareable. */
		     (1 << 10) |  /* ORGN0: normal, cacheable ... */
		     (1 << 8) |   /* IRGN0: normal, cacheable ... */
		     (2 << 6) |   /* SL0: Start at level 0. */
		     (20 << 0);   /* T0SZ: 44-bit input address size. */
	write_msr(vtcr_el2, v);

	/*
	 * 0    -> Device-nGnRnE memory
	 * 0xff -> Normal memory, Inner/Outer Write-Back Non-transient,
	 *         Write-Alloc, Read-Alloc.
	 */
	write_msr(mair_el2, (0 << (8 * STAGE1_DEVICEINDX)) |
				    (0xff << (8 * STAGE1_NORMALINDX)));

	write_msr(ttbr0_el2, table);

	/*
	 * Configure tcr_el2.
	 */
	v = (1 << 20) | /* TBI, top byte ignored. */
	    (2 << 16) | /* PS, Physical Address Size, 40 bits, 1TB. */
	    (0 << 14) | /* TG0, granule size, 4KB. */
	    (3 << 12) | /* SH0, inner shareable. */
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
	    (1 << 19) | /* WXN bit, writable execute never . */
	    (3 << 22) | /* RES1 bits. */
	    (3 << 28) | /* RES1 bits. */
	    0;

	__asm volatile("dsb sy");
	__asm volatile("isb");
	write_msr(sctlr_el2, v);
	__asm volatile("isb");
}
