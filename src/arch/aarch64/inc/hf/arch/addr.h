#pragma once

#include <stdint.h>

#define PAGE_BITS 12

/* Integer type large enough to hold a physical address. */
typedef uintptr_t uintpaddr_t;

/* Integer type large enough to hold a virtual address. */
typedef uintptr_t uintvaddr_t;
