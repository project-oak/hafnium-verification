#ifndef _ARCH_MM_H
#define _ARCH_MM_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* A phypiscal address. */
typedef size_t paddr_t;

/* A virtual address. */
typedef size_t vaddr_t;

/* A page table entry. */
typedef size_t pte_t;

#define PAGE_LEVEL_BITS 9
#define PAGE_BITS 12

struct arch_mm_ptable {
	int max_level;
};

/**
 * Initialises the architecture-dependents aspects of the page table.
 */
static inline void arch_mm_ptable_init(struct arch_mm_ptable *t)
{
	t->max_level = 2;
}

/**
 * Determines the maximum level supported by the given page table.
 */
static inline int arch_mm_max_level(struct arch_mm_ptable *t)
{
	return t->max_level;
}

/**
 * Converts a physical address to a table PTE.
 *
 * The spec says that 'Table descriptors for stage 2 translations do not
 * include any attribute field', so we don't take any attributes as arguments.
 */
static inline pte_t arch_mm_pa_to_table_pte(paddr_t pa)
{
	return pa | 0x3;
}

/**
 * Converts a physical address to a block PTE.
 */
static inline pte_t arch_mm_pa_to_block_pte(paddr_t pa, uint64_t attrs)
{
	return pa | attrs;
}

/**
 * Converts a physical address to a page PTE.
 */
static inline pte_t arch_mm_pa_to_page_pte(paddr_t pa, uint64_t attrs)
{
	return pa | attrs | ((attrs & 1) << 1);
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

/**
 * Clears the given virtual address, i.e., sets the ignored bits (from a page
 * table perspective) to zero.
 */
static inline vaddr_t arch_mm_clear_va(vaddr_t addr)
{
	return addr & ~((1ull << PAGE_BITS) - 1) & ((1ull << 48) - 1);
}

/**
 * Clears the given physical address, i.e., sets the ignored bits (from a page
 * table perspective) to zero.
 */
static inline paddr_t arch_mm_clear_pa(paddr_t addr)
{
	return addr & ~((1ull << PAGE_BITS) - 1) & ((1ull << 48) - 1);
}

/**
 * Extracts the physical address from a page table entry.
 */
static inline paddr_t arch_mm_pte_to_paddr(pte_t pte)
{
	return arch_mm_clear_pa(pte);
}

/**
 * Extracts a page table pointer from the given page table entry.
 */
static inline pte_t *arch_mm_pte_to_table(pte_t pte)
{
	return (pte_t *)arch_mm_pte_to_paddr(pte);
}

/**
 * Invalidates stage-1 TLB entries referring to the given virtual address range.
 */
static inline void arch_mm_invalidate_stage1_range(vaddr_t begin, vaddr_t end)
{
	vaddr_t it;

	begin >>= 12;
	end >>= 12;

	__asm__ volatile("dsb ishst");

	for (it = begin; it < end; it += (1ull << (PAGE_BITS - 12)))
		__asm__("tlbi vae2is, %0" : : "r"(it));

	__asm__ volatile("dsb ish");
}

/**
 * Invalidates stage-2 TLB entries referring to the given virtual address range.
 */
static inline void arch_mm_invalidate_stage2_range(vaddr_t begin, vaddr_t end)
{
	vaddr_t it;

	begin >>= 12;
	end >>= 12;

	__asm__ volatile("dsb ishst");

	for (it = begin; it < end; it += (1ull << (PAGE_BITS - 12)))
		__asm__("tlbi ipas2e1, %0" : : "r"(it));

	__asm__ volatile(
		"dsb ish\n"
		"tlbi vmalle1is\n"
		"dsb ish\n");
}

uint64_t arch_mm_mode_to_attrs(int mode);
void arch_mm_init(paddr_t table);

#endif /* _ARCH_MM_H */
