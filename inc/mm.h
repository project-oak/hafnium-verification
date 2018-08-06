#ifndef _MM_H
#define _MM_H

#include <stdbool.h>
#include <stdint.h>

#include "addr.h"
#include "arch_mm.h"

struct mm_ptable {
	paddr_t table;
	uint32_t id;
};

#define PAGE_SIZE (1 << PAGE_BITS)

/* The following are arch-independent page mapping modes. */
#define MM_MODE_R 0x01 /* read */
#define MM_MODE_W 0x02 /* write */
#define MM_MODE_X 0x04 /* execute */
#define MM_MODE_D 0x08 /* device */

/*
 * This flag indicates that memory allocation must not use locks. This is
 * relevant in systems where interlocked operations are only available after
 * virtual memory is enabled.
 */
#define MM_MODE_NOSYNC 0x10

/*
 * This flag indicates that the mapping is intended to be used in a first
 * stage translation table, which might have different encodings for the
 * attribute bits than the second stage table.
 */
#define MM_MODE_STAGE1 0x20

/*
 * This flag indicates that no TLB invalidations should be issued for the
 * changes in the page table.
 */
#define MM_MODE_NOINVALIDATE 0x40

bool mm_ptable_init(struct mm_ptable *t, uint32_t id, int mode);
void mm_ptable_dump(struct mm_ptable *t, int mode);
bool mm_ptable_identity_map(struct mm_ptable *t, vaddr_t begin, vaddr_t end,
			    int mode);
bool mm_ptable_identity_map_page(struct mm_ptable *t, vaddr_t va, int mode);
bool mm_ptable_unmap(struct mm_ptable *t, vaddr_t begin, vaddr_t end, int mode);
bool mm_ptable_is_mapped(struct mm_ptable *t, vaddr_t addr, int mode);
void mm_ptable_defrag(struct mm_ptable *t, int mode);
bool mm_ptable_unmap_hypervisor(struct mm_ptable *t, int mode);

bool mm_init(void);
bool mm_cpu_init(void);
bool mm_identity_map(vaddr_t begin, vaddr_t end, int mode);
bool mm_unmap(vaddr_t begin, vaddr_t end, int mode);
void mm_defrag(void);

/**
 * Converts an intermediate physical address to a physical address. Addresses
 * are currently identity mapped so this is a simple type convertion. Returns
 * true if the address was mapped in the table and the address was converted.
 */
static inline bool mm_ptable_translate_ipa(struct mm_ptable *t, ipaddr_t ipa,
					   paddr_t *pa)
{
	/* TODO: the ptable functions map physical to virtual addresses but they
	 * should really be mapping to intermediate physical addresses.
	 * It might be better to have different interfaces to the mm functions?
	 * This might also mean ipaddr_t should be used when building the VM
	 * tables too?
	 * */
	if (mm_ptable_is_mapped(t, va_init(ipa_addr(ipa)), 0)) {
		*pa = pa_init(ipa_addr(ipa));
		return true;
	}
	return false;
}

#endif /* _MM_H */
