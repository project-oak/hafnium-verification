#ifndef _ARCH_ADDR_H
#define _ARCH_ADDR_H

#include <stdint.h>

#define PAGE_LEVEL_BITS 9
#define PAGE_BITS 12

/* Integer type large enough to hold a physical address. */
typedef uintptr_t uintpaddr_t;

/* Integer type large enough to hold a virtual address. */
typedef uintptr_t uintvaddr_t;

/* A page table entry. */
typedef uint64_t pte_t;

#endif /* _ARCH_ADDR_H */
