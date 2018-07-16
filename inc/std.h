#ifndef _STD_H
#define _STD_H

#include <stddef.h>
#include <stdint.h>

void *memset(void *s, int c, size_t n);
void *memcpy(void *dst, const void *src, size_t n);
void *memmove(void *dst, const void *src, size_t n);
int memcmp(const void *a, const void *b, size_t n);

size_t strlen(const char *str);
int strcmp(const char *a, const char *b);

static inline uint16_t be16toh(uint16_t v)
{
	return v << 8 | v >> 8;
}

static inline uint32_t be32toh(uint32_t v)
{
	/* TODO: no conversion needed if native is big endian. */
	return (v << 24) |
	       (v >> 24) |
	       ((v & 0xff00) << 8) |
	       ((v & 0xff0000) >> 8);
}

static inline uint64_t be64toh(uint64_t v)
{
	/* TODO: no conversion needed if native is big endian. */
	return (v << 56) |
	       (v >> 56) |
	       ((v & 0xff00) << 40) |
	       ((v & 0xff000000000000) >> 40) |
	       ((v & 0xff0000) << 24) |
	       ((v & 0xff0000000000) >> 24) |
	       ((v & 0xff000000) << 8) |
	       ((v & 0xff00000000) >> 8);
}

static inline uint32_t htobe32(uint32_t v)
{
	return be32toh(v);
}

static inline uint64_t htobe64(uint64_t v)
{
	return be64toh(v);
}

#endif  /* STD_H */
