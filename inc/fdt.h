#ifndef _FDT_H
#define _FDT_H

#include <stdbool.h>
#include <stdint.h>

struct fdt_node {
	/* TODO: What do we need here? */
	const struct fdt_header *hdr;
	const char *begin;
	const char *end;
	const char *strs;
};

void fdt_dump(struct fdt_header *hdr);
void fdt_root_node(struct fdt_node *node, const struct fdt_header *hdr);
bool fdt_find_child(struct fdt_node *node, const char *child);
bool fdt_read_property(const struct fdt_node *node, const char *name,
		       const char **buf, uint32_t *size);

void fdt_add_mem_reservation(struct fdt_header *hdr, uint64_t addr, uint64_t len);

#endif  /* _FDT_H */
