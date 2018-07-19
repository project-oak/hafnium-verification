#include "fdt.h"

#include <stdint.h>

#include "dlog.h"
#include "std.h"

struct fdt_header {
	uint32_t magic;
	uint32_t totalsize;
	uint32_t off_dt_struct;
	uint32_t off_dt_strings;
	uint32_t off_mem_rsvmap;
	uint32_t version;
	uint32_t last_comp_version;
	uint32_t boot_cpuid_phys;
	uint32_t size_dt_strings;
	uint32_t size_dt_struct;
};

struct fdt_reserve_entry {
	uint64_t address;
	uint64_t size;
};

enum fdt_token {
	FDT_BEGIN_NODE = 1,
	FDT_END_NODE = 2,
	FDT_PROP = 3,
	FDT_NOP = 4,
	FDT_END = 9,
};

struct fdt_tokenizer {
	const char *cur;
	const char *end;
	const char *strs;
};

#define FDT_VERSION 17
#define FDT_MAGIC 0xd00dfeed

static void fdt_tokenizer_init(struct fdt_tokenizer *t, const char *strs,
			       const char *begin, const char *end)
{
	t->strs = strs;
	t->cur = begin;
	t->end = end;
}

static void fdt_tokenizer_align(struct fdt_tokenizer *t)
{
	t->cur = (char *)(((size_t)t->cur + 3) & ~3);
}

static bool fdt_tokenizer_uint32(struct fdt_tokenizer *t, uint32_t *res)
{
	const char *next = t->cur + sizeof(*res);
	if (next > t->end) {
		return false;
	}

	*res = be32toh(*(uint32_t *)t->cur);
	t->cur = next;

	return true;
}

static bool fdt_tokenizer_token(struct fdt_tokenizer *t, uint32_t *res)
{
	uint32_t v;

	while (fdt_tokenizer_uint32(t, &v)) {
		if (v != FDT_NOP) {
			*res = v;
			return true;
		}
	}
	return false;
}

static bool fdt_tokenizer_bytes(struct fdt_tokenizer *t, const char **res,
				size_t size)
{
	const char *next = t->cur + size;
	if (next > t->end) {
		return false;
	}

	*res = t->cur;
	t->cur = next;
	fdt_tokenizer_align(t);

	return true;
}

static bool fdt_tokenizer_str(struct fdt_tokenizer *t, const char **res)
{
	const char *p;
	for (p = t->cur; p < t->end; p++) {
		if (!*p) {
			/* Found the end of the string. */
			*res = t->cur;
			t->cur = p + 1;
			fdt_tokenizer_align(t);
			return true;
		}
	}

	return false;
}

bool fdt_root_node(struct fdt_node *node, const struct fdt_header *hdr)
{
	uint32_t max_ver;
	uint32_t min_ver;
	uint32_t begin = be32toh(hdr->off_dt_struct);
	uint32_t size = be32toh(hdr->size_dt_struct);

	memset(node, 0, sizeof(*node));

	/* Check the magic number before anything else. */
	if (hdr->magic != be32toh(FDT_MAGIC)) {
		return false;
	}

	/* Check the version. */
	max_ver = be32toh(hdr->version);
	min_ver = be32toh(hdr->last_comp_version);
	if (FDT_VERSION < min_ver || FDT_VERSION > max_ver) {
		return false;
	}

	/* TODO: Verify that it is all within the fdt. */
	node->begin = (const char *)hdr + begin;
	node->end = node->begin + size;

	/* TODO: Verify strings as well. */
	node->strs = (char *)hdr + be32toh(hdr->off_dt_strings);

	return true;
}

static bool fdt_next_property(struct fdt_tokenizer *t, const char **name,
			      const char **buf, uint32_t *size)
{
	uint32_t token;
	uint32_t nameoff;

	if (!fdt_tokenizer_token(t, &token)) {
		return false;
	}

	if (token != FDT_PROP) {
		/* Rewind so that caller will get the same token. */
		t->cur -= sizeof(uint32_t);
		return false;
	}

	if (!fdt_tokenizer_uint32(t, size) ||
	    !fdt_tokenizer_uint32(t, &nameoff) ||
	    !fdt_tokenizer_bytes(t, buf, *size)) {
		/*
		 * Move cursor to the end so that caller won't get any new
		 * tokens.
		 */
		t->cur = t->end;
		return false;
	}

	/* TODO: Need to verify the strings. */
	*name = t->strs + nameoff;

	return true;
}

static bool fdt_next_subnode(struct fdt_tokenizer *t, const char **name)
{
	uint32_t token;

	if (!fdt_tokenizer_token(t, &token)) {
		return false;
	}

	if (token != FDT_BEGIN_NODE) {
		/* Rewind so that caller will get the same token. */
		t->cur -= sizeof(uint32_t);
		return false;
	}

	if (!fdt_tokenizer_str(t, name)) {
		/*
		 * Move cursor to the end so that caller won't get any new
		 * tokens.
		 */
		t->cur = t->end;
		return false;
	}

	return true;
}

static void fdt_skip_properties(struct fdt_tokenizer *t)
{
	const char *name;
	const char *buf;
	uint32_t size;
	while (fdt_next_property(t, &name, &buf, &size)) {
		/* do nothing */
	}
}

static bool fdt_skip_node(struct fdt_tokenizer *t)
{
	const char *name;
	uint32_t token;
	size_t pending = 1;

	fdt_skip_properties(t);

	do {
		while (fdt_next_subnode(t, &name)) {
			fdt_skip_properties(t);
			pending++;
		}

		if (!fdt_tokenizer_token(t, &token)) {
			return false;
		}

		if (token != FDT_END_NODE) {
			t->cur = t->end;
			return false;
		}

		pending--;
	} while (pending);

	return true;
}

bool fdt_read_property(const struct fdt_node *node, const char *name,
		       const char **buf, uint32_t *size)
{
	struct fdt_tokenizer t;
	const char *prop_name;

	fdt_tokenizer_init(&t, node->strs, node->begin, node->end);

	while (fdt_next_property(&t, &prop_name, buf, size)) {
		if (!strcmp(prop_name, name)) {
			return true;
		}
	}

	return false;
}

bool fdt_first_child(struct fdt_node *node, const char **child_name)
{
	struct fdt_tokenizer t;

	fdt_tokenizer_init(&t, node->strs, node->begin, node->end);

	fdt_skip_properties(&t);

	if (!fdt_next_subnode(&t, child_name)) {
		return false;
	}

	node->begin = t.cur;

	return true;
}

bool fdt_next_sibling(struct fdt_node *node, const char **sibling_name)
{
	struct fdt_tokenizer t;

	fdt_tokenizer_init(&t, node->strs, node->begin, node->end);

	if (!fdt_skip_node(&t)) {
		return false;
	}

	if (!fdt_next_subnode(&t, sibling_name)) {
		return false;
	}

	node->begin = t.cur;

	return true;
}

bool fdt_find_child(struct fdt_node *node, const char *child)
{
	struct fdt_tokenizer t;
	const char *name;

	fdt_tokenizer_init(&t, node->strs, node->begin, node->end);

	fdt_skip_properties(&t);

	while (fdt_next_subnode(&t, &name)) {
		if (!strcmp(name, child)) {
			node->begin = t.cur;
			return true;
		}

		fdt_skip_node(&t);
	}

	return false;
}

void fdt_dump(struct fdt_header *hdr)
{
	uint32_t token;
	size_t depth = 0;
	const char *name;
	struct fdt_tokenizer t;
	struct fdt_node node;

	/* Traverse the whole thing. */
	fdt_root_node(&node, hdr);

	fdt_tokenizer_init(&t, node.strs, node.begin, node.end);

	do {
		while (fdt_next_subnode(&t, &name)) {
			const char *buf;
			uint32_t size;

			dlog("%*sNew node: \"%s\"\n", 2 * depth, "", name);
			depth++;
			while (fdt_next_property(&t, &name, &buf, &size)) {
				size_t i;
				dlog("%*sproperty: \"%s\" (", 2 * depth, "",
				     name);
				for (i = 0; i < size; i++) {
					dlog("%s%02x", i == 0 ? "" : " ",
					     buf[i]);
				}
				dlog(")\n");
			}
		}

		if (!fdt_tokenizer_token(&t, &token)) {
			return;
		}

		if (token != FDT_END_NODE) {
			return;
		}

		depth--;
	} while (depth);

	dlog("fdt: off_mem_rsvmap=%u\n", be32toh(hdr->off_mem_rsvmap));
	{
		struct fdt_reserve_entry *e =
			(struct fdt_reserve_entry
				 *)((size_t)hdr + be32toh(hdr->off_mem_rsvmap));
		while (e->address || e->size) {
			dlog("Entry: %p (0x%x bytes)\n", be64toh(e->address),
			     be64toh(e->size));
			e++;
		}
	}
}

void fdt_add_mem_reservation(struct fdt_header *hdr, size_t addr, size_t len)
{
	/* TODO: Clean this up. */
	char *begin = (char *)hdr + be32toh(hdr->off_mem_rsvmap);
	struct fdt_reserve_entry *e = (struct fdt_reserve_entry *)begin;
	hdr->totalsize = htobe32(be32toh(hdr->totalsize) +
				 sizeof(struct fdt_reserve_entry));
	hdr->off_dt_struct = htobe32(be32toh(hdr->off_dt_struct) +
				     sizeof(struct fdt_reserve_entry));
	hdr->off_dt_strings = htobe32(be32toh(hdr->off_dt_strings) +
				      sizeof(struct fdt_reserve_entry));
	memmove(begin + sizeof(struct fdt_reserve_entry), begin,
		be32toh(hdr->totalsize) - be32toh(hdr->off_mem_rsvmap));
	e->address = htobe64(addr);
	e->size = htobe64(len);
}

size_t fdt_header_size(void)
{
	return sizeof(struct fdt_header);
}

size_t fdt_total_size(struct fdt_header *hdr)
{
	return be32toh(hdr->totalsize);
}
