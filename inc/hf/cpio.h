#pragma once

#include <stdbool.h>
#include <stddef.h>

#include "hf/memiter.h"

bool cpio_next(struct memiter *iter, const char **name, const void **contents,
	       size_t *size);
