#pragma once

#include <stddef.h>
#include <stdint.h>

#include "hf/cpio.h"
#include "hf/memiter.h"
#include "hf/mm.h"

bool load_primary(const struct memiter *cpio, size_t kernel_arg,
		  struct memiter *initrd);
bool load_secondary(const struct memiter *cpio, paddr_t mem_begin,
		    paddr_t *mem_end);
