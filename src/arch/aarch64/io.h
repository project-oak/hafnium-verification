#ifndef _IO_H
#define _IO_H

#include <stddef.h>
#include <stdint.h>

#include "hf/arch/barriers.h"

static inline uint32_t io_read(size_t addr)
{
	return *(volatile uint32_t *)addr;
}

static inline uint32_t io_read_mb(size_t addr)
{
	uint32_t v = io_read(addr);
	dsb();
	isb();
	return v;
}

static inline void io_write(size_t addr, uint32_t v)
{
	*(volatile uint32_t *)addr = v;
}

static inline void io_write_mb(size_t addr, uint32_t v)
{
	dsb();
	isb();
	io_write(addr, v);
}

#endif /* _IO_H */
