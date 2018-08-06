#ifndef _ADDR_H
#define _ADDR_H

#include <stddef.h>
#include <stdint.h>

#include "arch_addr.h"

/* An opaque type for a physical address. */
typedef struct {
	uintpaddr_t pa;
} paddr_t;

/* An opaque type for an intermediate physical address. */
typedef struct {
	uintpaddr_t ipa;
} ipaddr_t;

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
 * Initializes an intermeditate physical address.
 */
static inline ipaddr_t ipa_init(uintvaddr_t v)
{
	return (ipaddr_t){.ipa = v};
}

/**
 * Extracts the absolute intermediate physical address.
 */
static inline uintpaddr_t ipa_addr(ipaddr_t ipa)
{
	return ipa.ipa;
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

/**
 * Casts a physical address to a virtual address.
 */
static inline vaddr_t va_from_pa(paddr_t pa)
{
	return va_init(pa_addr(pa));
}

/**
 * Casts a physical address to an intermediate physical address.
 */
static inline ipaddr_t ipa_from_pa(paddr_t pa)
{
	return ipa_init(pa_addr(pa));
}

/**
 * Casts a virtual address to a physical address.
 */
static inline paddr_t pa_from_va(vaddr_t va)
{
	return pa_init(va_addr(va));
}

/**
 * Casts a pointer to a virtual address.
 */
static inline vaddr_t va_from_ptr(const void *p)
{
	return (vaddr_t){.va = (uintvaddr_t)p};
}

/**
 * Casts a virtual address to a pointer. Only use when the virtual address is
 * mapped for the calling context.
 * TODO: check the mapping for a range and return a memiter?
 */
static inline void *ptr_from_va(vaddr_t va)
{
	return (void *)va_addr(va);
}

#endif /* _ADDR_H */
