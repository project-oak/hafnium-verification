#ifndef _MM_H
#define _MM_H

#include <stdbool.h>

#include "arch_mm.h"

struct mm_ptable {
	struct arch_mm_ptable arch;
	pte_t *table;
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

bool mm_ptable_init(struct mm_ptable *t, int mode);
void mm_ptable_dump(struct mm_ptable *t);
bool mm_ptable_map(struct mm_ptable *t, vaddr_t vaddr_begin, vaddr_t vaddr_end,
		   paddr_t paddr, int mode);
bool mm_ptable_map_page(struct mm_ptable *t, vaddr_t va, paddr_t pa, int mode);
bool mm_ptable_unmap(struct mm_ptable *t, vaddr_t begin, vaddr_t end, int mode);
void mm_ptable_defrag(struct mm_ptable *t);

#endif /* _MM_H */
