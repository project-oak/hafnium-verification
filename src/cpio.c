#include "hf/cpio.h"

#include <stdint.h>

#include "hf/std.h"

#pragma pack(push, 1)
struct cpio_header {
	uint16_t magic;
	uint16_t dev;
	uint16_t ino;
	uint16_t mode;
	uint16_t uid;
	uint16_t gid;
	uint16_t nlink;
	uint16_t rdev;
	uint16_t mtime[2];
	uint16_t namesize;
	uint16_t filesize[2];
};
#pragma pack(pop)

/**
 * Retrieves the next file stored in the cpio archive stored in the cpio, and
 * advances the iterator such that another call to this function would return
 * the following file.
 */
bool cpio_next(struct memiter *iter, const char **name, const void **contents,
	       size_t *size)
{
	size_t len;
	struct memiter lit = *iter;
	const struct cpio_header *h = (const struct cpio_header *)lit.next;

	if (!memiter_advance(&lit, sizeof(struct cpio_header))) {
		return false;
	}

	*name = lit.next;

	/* TODO: Check magic. */

	len = (h->namesize + 1) & ~1;
	if (!memiter_advance(&lit, len)) {
		return false;
	}

	*contents = lit.next;

	len = (size_t)h->filesize[0] << 16 | h->filesize[1];
	if (!memiter_advance(&lit, (len + 1) & ~1)) {
		return false;
	}

	/* TODO: Check that string is null-terminated. */

	/* Stop enumerating files when we hit the end marker. */
	if (!strcmp(*name, "TRAILER!!!")) {
		return false;
	}

	*size = len;
	*iter = lit;

	return true;
}
