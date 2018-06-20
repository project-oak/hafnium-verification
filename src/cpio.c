#include "cpio.h"

#include <stdint.h>

#include "std.h"

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

void cpio_init(struct cpio *c, const void *buf, size_t size)
{
	c->first = buf;
	c->total_size = size;
}

void cpio_init_iter(struct cpio *c, struct cpio_iter *iter)
{
	iter->cur = c->first;
	iter->size_left = c->total_size;
}

bool cpio_next(struct cpio_iter *iter, const char **name,
	       const void **contents, size_t *size)
{
	const struct cpio_header *h = iter->cur;
	size_t size_left;
	size_t filelen;
	size_t namelen;

	size_left = iter->size_left;
	if (size_left < sizeof(struct cpio_header))
		return false;

	/* TODO: Check magic. */

	size_left -= sizeof(struct cpio_header);
	namelen = (h->namesize + 1) & ~1;
	if (size_left < namelen)
		return false;

	size_left -= namelen;
	filelen = (size_t)h->filesize[0] << 16 | h->filesize[1];
	if (size_left < filelen)
		return false;

	/* TODO: Check that string is null-terminated. */
	/* TODO: Check that trailler is not returned. */

	/* Stop enumerating files when we hit the end marker. */
	if (!strcmp((const char *)(iter->cur + 1), "TRAILER!!!"))
		return false;

	size_left -= filelen;

	*name = (const char *)(iter->cur + 1);
	*contents = *name + namelen;
	*size = filelen;

	iter->cur = (struct cpio_header *)((char *)*contents + filelen);
	iter->cur = (struct cpio_header *)(char *)(((size_t)iter->cur + 1) & ~1);
	iter->size_left = size_left;

	return true;
}
