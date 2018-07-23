#ifndef _LOAD_H
#define _LOAD_H

#include <stddef.h>
#include <stdint.h>

#include "cpio.h"
#include "memiter.h"

bool load_primary(const struct memiter *cpio, size_t kernel_arg,
		  struct memiter *initrd);
bool load_secondary(const struct memiter *cpio, uint64_t mem_begin,
		    uint64_t *mem_end);

#endif /* _LOAD_H */
