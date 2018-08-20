#include "hf/std.h"

void *memset(void *s, int c, size_t n)
{
	char *p = (char *)s;
	while (n--) {
		*p++ = c;
	}
	return s;
}

/*
 * Calculates the length of the provided null-terminated string.
 */
size_t strlen(const char *str)
{
	const char *p = str;
	while (*p) {
		p++;
	}
	return p - str;
}

void *memcpy(void *dst, const void *src, size_t n)
{
	char *x = dst;
	const char *y = src;

	while (n--) {
		*x = *y;
		x++;
		y++;
	}

	return dst;
}

void *memmove(void *dst, const void *src, size_t n)
{
	char *x;
	const char *y;

	if (dst < src) {
		return memcpy(dst, src, n);
	}

	x = (char *)dst + n - 1;
	y = (const char *)src + n - 1;

	while (n--) {
		*x = *y;
		x--;
		y--;
	}

	return dst;
}

int memcmp(const void *a, const void *b, size_t n)
{
	const char *x = a;
	const char *y = b;

	while (n--) {
		if (*x != *y) {
			return *x - *y;
		}
		x++;
		y++;
	}

	return 0;
}

int strcmp(const char *a, const char *b)
{
	const char *x = a;
	const char *y = b;

	while (*x != 0 && *y != 0) {
		if (*x != *y) {
			return *x - *y;
		}
		x++;
		y++;
	}

	return *x - *y;
}
