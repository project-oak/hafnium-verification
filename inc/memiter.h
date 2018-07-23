#ifndef _MEMITER_H
#define _MEMITER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct memiter {
	const char *next;
	const char *limit;
};

void memiter_init(struct memiter *it, const void *data, size_t size);
bool memiter_parse_uint(struct memiter *it, uint64_t *value);
bool memiter_parse_str(struct memiter *it, struct memiter *str);
bool memiter_iseq(const struct memiter *it, const char *str);
bool memiter_advance(struct memiter *it, size_t v);

#endif /* _MEMITER_H */
