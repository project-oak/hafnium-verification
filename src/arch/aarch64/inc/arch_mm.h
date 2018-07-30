#ifndef _ARCH_MM_H
#define _ARCH_MM_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Integer type large enough to hold a physical address. */
typedef uintptr_t uintpaddr_t;

/* Integer type large enough to hold a virtual address. */
typedef uintptr_t uintvaddr_t;

/* A page table entry. */
typedef uint64_t pte_t;

/* An opaque type for a physical address. */
typedef struct {
	uintpaddr_t pa;
} paddr_t;

/* An opaque type for a virtual address. */
typedef struct {
	uintvaddr_t va;
} vaddr_t;

/**
 * Initializes a physical address.
 */
static inline paddr_t pa_init(uintpaddr_t p)
{
	return (paddr_t){.pa = p};
}

/**
 * Extracts the absolute physical address.
 */
static inline uintpaddr_t pa_addr(paddr_t pa)
{
	return pa.pa;
}

/**
 * Initializes a virtual address.
 */
static inline vaddr_t va_init(uintvaddr_t v)
{
	return (vaddr_t){.va = v};
}

/**
 * Extracts the absolute virtual address.
 */
static inline uintvaddr_t va_addr(vaddr_t va)
{
	return va.va;
}

/**
 * Advances a virtual address.
 */
static inline vaddr_t va_add(vaddr_t va, size_t n)
{
	return va_init(va_addr(va) + n);
}

#define PAGE_LEVEL_BITS 9
#define PAGE_BITS 12

/**
 * Converts a physical address to a table PTE.
 *
 * The spec says that 'Table descriptors for stage 2 translations do not
 * include any attribute field', so we don't take any attributes as arguments.
 */
static inline pte_t arch_mm_pa_to_table_pte(paddr_t pa)
{
	return pa_addr(pa) | 0x3;
}

/**
 * Converts a physical address to a block PTE.
 */
static inline pte_t arch_mm_pa_to_block_pte(paddr_t pa, uint64_t attrs)
{
	return pa_addr(pa) | attrs;
}

/**
 * Converts a physical address to a page PTE.
 */
static inline pte_t arch_mm_pa_to_page_pte(paddr_t pa, uint64_t attrs)
{
	return pa_addr(pa) | attrs | ((attrs & 1) << 1);
}

/**
 * Converts a block PTE to a page PTE.
 */
static inline pte_t arch_mm_block_to_page_pte(pte_t pte)
{
	return pte | 2;
}

/**
 * Specifies whether block mappings are acceptable at the given level.
 */
static inline bool arch_mm_is_block_allowed(int level)
{
	return level == 1 || level == 2;
}

/**
 * Returns the encoding of a page table entry that isn't present.
 */
static inline pte_t arch_mm_absent_pte(void)
{
	return 0;
}

/**
 * Determines if the given pte is present, i.e., if it points to another table,
 * to a page, or a block of pages.
 */
static inline bool arch_mm_pte_is_present(pte_t pte)
{
	return (pte & 1) != 0;
}

/**
 * Determines if the given pte references another table.
 */
static inline bool arch_mm_pte_is_table(pte_t pte)
{
	return (pte & 3) == 3;
}

/**
 * Determines if the given pte references a block of pages.
 */
static inline bool arch_mm_pte_is_block(pte_t pte)
{
	return (pte & 3) == 1;
}

#define CLEAR_PTE_ATTRS(v) \
	((v) & ~((1ull << PAGE_BITS) - 1) & ((1ull << 48) - 1))

/**
 * Clears the given virtual address, i.e., sets the ignored bits (from a page
 * table perspective) to zero.
 */
static inline vaddr_t arch_mm_clear_va(vaddr_t va)
{
	return va_init(CLEAR_PTE_ATTRS(va_addr(va)));
}

/**
 * Clears the given physical address, i.e., sets the ignored bits (from a page
 * table perspective) to zero.
 */
static inline paddr_t arch_mm_clear_pa(paddr_t pa)
{
	return pa_init(CLEAR_PTE_ATTRS(pa_addr(pa)));
}

/**
 * Extracts the physical address from a page table entry.
 */
static inline paddr_t arch_mm_pte_to_paddr(pte_t pte)
{
	return pa_init(CLEAR_PTE_ATTRS(pte));
}

/**
 * Extracts a page table pointer from the given page table entry.
 */
static inline pte_t *arch_mm_pte_to_table(pte_t pte)
{
	return (pte_t *)CLEAR_PTE_ATTRS(pte);
}

#undef CLEAR_PTE_ATTRS

/**
 * Invalidates stage-1 TLB entries referring to the given virtual address range.
 */
static inline void arch_mm_invalidate_stage1_range(vaddr_t va_begin,
						   vaddr_t va_end)
{
	uintvaddr_t begin = va_addr(va_begin);
	uintvaddr_t end = va_addr(va_end);
	uintvaddr_t it;

	begin >>= 12;
	end >>= 12;

	__asm__ volatile("dsb ishst");

	for (it = begin; it < end; it += (1ull << (PAGE_BITS - 12))) {
		__asm__("tlbi vae2is, %0" : : "r"(it));
	}

	__asm__ volatile("dsb ish");
}

/**
 * Invalidates stage-2 TLB entries referring to the given virtual address range.
 */
static inline void arch_mm_invalidate_stage2_range(vaddr_t va_begin,
						   vaddr_t va_end)
{
	uintvaddr_t begin = va_addr(va_begin);
	uintvaddr_t end = va_addr(va_end);
	uintvaddr_t it;

	/* TODO: This only applies to the current VMID. */

	begin >>= 12;
	end >>= 12;

	__asm__ volatile("dsb ishst");

	for (it = begin; it < end; it += (1ull << (PAGE_BITS - 12))) {
		__asm__("tlbi ipas2e1, %0" : : "r"(it));
	}

	__asm__ volatile(
		"dsb ish\n"
		"tlbi vmalle1is\n"
		"dsb ish\n");
}

static inline void arch_mm_set_vm(uint64_t vmid, paddr_t table)
{
	__asm__ volatile("msr vttbr_el2, %0"
			 :
			 : "r"(pa_addr(table) | (vmid << 48)));
}

uint64_t arch_mm_mode_to_attrs(int mode);
bool arch_mm_init(paddr_t table, bool first);
int arch_mm_max_level(int mode);

#endif /* _ARCH_MM_H */
