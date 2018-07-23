#ifndef _CPIO_H
#define _CPIO_H

#include <stdbool.h>
#include <stddef.h>

#include "memiter.h"

bool cpio_next(struct memiter *iter, const char **name, const void **contents,
	       size_t *size);

#endif /* _CPIO_H */
