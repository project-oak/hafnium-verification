#ifndef _CPIO_H
#define _CPIO_H

#include <stdbool.h>
#include <stddef.h>

struct cpio {
	const struct cpio_header *first;
	size_t total_size;
};

struct cpio_iter {
	const struct cpio_header *cur;
	size_t size_left;
};

void cpio_init(struct cpio *c, const void *buf, size_t size);
void cpio_init_iter(struct cpio *c, struct cpio_iter *iter);
bool cpio_next(struct cpio_iter *iter, const char **name, const void **contents,
	       size_t *size);

#endif /* _CPIO_H */
