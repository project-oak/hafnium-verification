#include "arch_cpu.h"
#include "msr.h"

void arch_vptable_init(struct arch_page_table *table)
{
	uint64_t i;
	uint64_t v;

	/* TODO: Check each bit. */
	for (i = 0; i < 512; i++) {
		table->entry0[i] = 1 |
			(i << 30) | /* Address */
			(1 << 10) | /* Access flag. */
			(0 << 8) | /* sh: non-shareable. this preserves EL1. */
			(3 << 6) | /* rw */
			(0xf << 2); /* normal mem; preserves EL0/1. */
		table->entry1[i] = 1 |
			((i+512) << 30) | /* Address */
			(1 << 10) | /* Access flag. */
			(0 << 8) | /* sh: non-shareable. this preserves EL1. */
			(3 << 6) | /* rw */
			(0xf << 2); /* normal mem; preserves EL0/1. */
		table->first[i] = 0;
	}

	table->first[0] = (uint64_t)&table->entry0[0] | 3;
	table->first[1] = (uint64_t)&table->entry1[0] | 3;

	/* TODO: Where should this go? */
	v =
		(1u << 31) | /* RES1. */
		(4 << 16) | /* PS: 44 bits. */
		(0 << 14) | /* TG0: 4 KB granule. */
		(3 << 12) | /* SH0: inner shareable. */
		(1 << 10) | /* ORGN0: normal, cacheable ... */
		(1 << 8) | /* IRGN0: normal, cacheable ... */
		(2 << 6) | /* SL0: Start at level 0. */
		(20 << 0); /* T0SZ: 44-bit input address size. */
	write_msr(vtcr_el2, v);
}

#if 0
#include "arch.h"

#include <stdint.h>

#include "alloc.h"
#include "log.h"
#include "msr.h"

#define PAGE_BITS 12
#define PAGE_SIZE (1 << PAGE_BITS)
#define ENTRIES_PER_LEVEL (PAGE_SIZE / sizeof(uint64_t))
#define INITIAL_LEVEL 1

extern char text_begin[];
extern char text_end[];
extern char rodata_begin[];
extern char rodata_end[];
extern char data_begin[];
extern char data_end[];
extern char bin_end[];

static uint64_t *ttbr;

static inline size_t mm_entry_size(int level)
{
	return 1ull << (PAGE_BITS + (3 - level) * (PAGE_BITS - 3));
}

static inline size_t mm_level_end(size_t va, int level)
{
	size_t offset = (PAGE_BITS + (4 - level) * (PAGE_BITS - 3));
	return ((va >> offset) + 1) << offset;
}

static inline size_t mm_index(size_t va, int level)
{
	size_t v = va >> (PAGE_BITS + (3 - level) * (PAGE_BITS - 3));
	return v & ((1 << (PAGE_BITS - 3)) - 1);
}

static inline uint64_t mm_clear_attrs(uint64_t v)
{
	/* Clean bottom bits. */
	v &= ~((1 << PAGE_BITS) - 1);

	/* Clean top bits. */
	v &= ((1ull << 59) - 1);

	return v;
}

static inline uint64_t *mm_table_ptr(uint64_t pa)
{
	return (uint64_t *)mm_clear_attrs(pa);
}

static inline uint64_t mm_mode_to_attrs(uint64_t mode)
{
	uint64_t attrs =
		(1 << 10) | /* Access flag. */
		(2 << 8); /* sh -> outer shareable. */

	/* TODO: This is different in s2. */
	if (!(mode & MM_X)) {
		attrs |= (1ull << 54); /* XN or UXN, [user] execute never. */

		/* TODO: This is only ok in EL1, it is RES0 in EL2. */
		attrs |= (1ull << 53); /* PXN, privileged execute never. */
	}

	/* TODO: This is different in s2. */
	if (mode & MM_W)
		attrs |= (0 << 6); /* rw, no EL0 access. */
	else
		attrs |= (2 << 6); /* read-only, no EL0 access. */

	if (mode & MM_D)
		attrs |= (0 << 2); /* device memory in MAIR_ELx. */
	else
		attrs |= (1 << 2); /* normal memory in MAIR_ELx. */

	return attrs;
}

static uint64_t *mm_populate_table(uint64_t *table, uint64_t index)
{
	uint64_t *ntable;
	uint64_t v = table[index];
	uint64_t i;

	/* Check if table entry already exists. */
	if (v & 1) {
		/* Fail if it's a block one. */
		if (!(v & 2))
			return NULL;
		return mm_table_ptr(v);
	}

	/* Allocate a new table entry and initialize it. */
	ntable = halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	if (!ntable)
		return NULL;

	for (i = 0; i < ENTRIES_PER_LEVEL; i++)
		ntable[i] = 0;

	/* Fill in the new entry. */
	table[index] = (size_t)ntable | 0x3;

	return ntable;
}

static bool mm_map_level(size_t va, size_t va_end, size_t pa,
			 uint64_t attrs, uint64_t *table, int level)
{
	size_t i = mm_index(va, level);
	size_t va_level_end = mm_level_end(va, level);
	size_t entry_size = mm_entry_size(level);

	/* Cap va_end so that we don't go over of the current level max. */
	if (va_end > va_level_end)
		va_end = va_level_end;

	/* Fill each entry in the table. */
	while (va < va_end) {
		if (level == 3) {
			table[i] = pa | 0x3 | attrs;
		} else {
			uint64_t *nt = mm_populate_table(table, i);
			if (!nt) {
				/* TODO: Undo all the work so far? */
				return false;
			}

			if (!mm_map_level(va, va_end, pa, attrs, nt, level+1)) {
				/* TODO: Undo all the work so far? */
				return false;
			}
		}

		va += entry_size;
		pa += entry_size;
		i++;
	}

	return true;
}

bool mm_map_range(size_t va, size_t size, uint64_t pa, uint64_t mode)
{
	uint64_t attrs = mm_mode_to_attrs(mode);
	uint64_t end = mm_clear_attrs(va + size + PAGE_SIZE - 1);

	va = mm_clear_attrs(va);
	pa = mm_clear_attrs(pa);

	return mm_map_level(va, end, pa, attrs, ttbr, INITIAL_LEVEL);
}

bool mm_map_page(size_t va, size_t pa, uint64_t mode)
{
	size_t i;
	uint64_t attrs = mm_mode_to_attrs(mode);
	uint64_t *table = ttbr;

	va = mm_clear_attrs(va);
	pa = mm_clear_attrs(pa);
	for (i = INITIAL_LEVEL; i < 3; i++) {
		table = mm_populate_table(table, mm_index(va, i));
		if (!table)
			return false;
	}

	/* We reached level 3. */
	i = mm_index(va, 3);
	table[i] = pa | 0x3 | attrs;
	return true;
}

bool arch_init_mm(void)
{
#if 0
	size_t i;

	/* Allocate the first level, then zero it out. */
	ttbr = halloc_aligned(PAGE_SIZE, PAGE_SIZE);
	if (!ttbr)
		return false;

	for (i = 0; i < ENTRIES_PER_LEVEL; i++)
		ttbr[i] = 0;

	/* Map page for uart. */
	mm_map_page(PL011_BASE, PL011_BASE, MM_R | MM_W | MM_D);

	/* Map page for gic. */
	mm_map_page(GICD_BASE, GICD_BASE, MM_R | MM_W | MM_D);
	mm_map_page(GICC_BASE, GICC_BASE, MM_R | MM_W | MM_D);

	/* Map each section. */
	mm_map_range((size_t)text_begin, text_end - text_begin,
		     (size_t)text_begin,  MM_X);

	mm_map_range((size_t)rodata_begin, rodata_end - rodata_begin,
		     (size_t)rodata_begin, MM_R);

	mm_map_range((size_t)data_begin, data_end - data_begin,
		     (size_t)data_begin, MM_R | MM_W);

	mm_map_range((size_t)bin_end, 20 * 1024 * 1024, (size_t)bin_end,
		     MM_R | MM_W);
#endif
	log(INFO, "About to enable mmu.\n");
	enable_mmu(ttbr);
	log(INFO, "mmu is on.\n");

	return true;
}

static void arch_mm_dump_table(uint64_t *table, int level)
{
	uint64_t i, j;
	for (i = 0; i < ENTRIES_PER_LEVEL; i++) {
		if ((table[i] & 1) == 0)
			continue;

		for (j = 1 * (level - INITIAL_LEVEL + 1); j; j--)
			log(INFO, "\t");
		log(INFO, "%x: %x\n", i, table[i]);
		if (level >= 3)
			continue;

		if ((table[i] & 3) == 3)
			arch_mm_dump_table(mm_table_ptr(table[i]), level + 1);
	}
}

void enable_mmu(uint64_t *table)
{
	//uint32_t v;

	enable_s2();
#if 0
	/*
	 * 0 -> Device-nGnRnE memory
	 * 1 -> Normal memory, Inner/Outer Write-Back Non-transient,
	 *      Write-Alloc, Read-Alloc.
	 */
	write_msr(mair_el2, 0xff00);
	write_msr(ttbr0_el2, table);

	/*
	 * Configure tcr_el2.
	 */
	v =
		(1 << 20) | /* TBI, top byte ignored. */
		(2 << 16) | /* PS, Physical Address Size, 40 bits, 1TB. */
		(0 << 14) | /* TG0, granule size, 4KB. */
		(3 << 12) | /* SH0, inner shareable. */
		(1 << 10) | /* ORGN0, normal mem, WB RA WA Cacheable. */
		(1 << 8) |  /* IRGN0, normal mem, WB RA WA Cacheable. */
		(25 << 0) | /* T0SZ, input address is 2^39 bytes. */
		0;
	write_msr(tcr_el2, v);

	v =
		(1 << 0) | /* M, enable stage 1 EL2 MMU. */
		(1 << 1) | /* A, enable alignment check faults. */
		// TODO: Enable this.
//		(1 << 2) | /* C, data cache enable. */
		(1 << 3) | /* SA, enable stack alignment check. */
		(3 << 4) | /* RES1 bits. */
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
#endif
}
#endif
