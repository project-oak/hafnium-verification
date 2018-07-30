#include "fdt_handler.h"

#include "boot_params.h"
#include "dlog.h"
#include "fdt.h"
#include "mm.h"
#include "std.h"

static uint64_t convert_number(const char *data, uint32_t size)
{
	union {
		volatile uint64_t v;
		char a[8];
	} t;

	switch (size) {
	case sizeof(uint32_t):
		return be32toh(*(uint32_t *)data);
	case sizeof(uint64_t):
		memcpy(t.a, data, sizeof(uint64_t));
		return be64toh(t.v);
	default:
		return 0;
	}
}

static bool fdt_read_number(const struct fdt_node *node, const char *name,
			    uint64_t *value)
{
	const char *data;
	uint32_t size;

	if (!fdt_read_property(node, name, &data, &size)) {
		return false;
	}

	switch (size) {
	case sizeof(uint32_t):
	case sizeof(uint64_t):
		*value = convert_number(data, size);
		break;

	default:
		return false;
	}

	return true;
}

static bool fdt_write_number(struct fdt_node *node, const char *name,
			     uint64_t value)
{
	const char *data;
	uint32_t size;
	union {
		volatile uint64_t v;
		char a[8];
	} t;

	if (!fdt_read_property(node, name, &data, &size)) {
		return false;
	}

	switch (size) {
	case sizeof(uint32_t):
		*(uint32_t *)data = be32toh(value);
		break;

	case sizeof(uint64_t):
		t.v = be64toh(value);
		memcpy((void *)data, t.a, sizeof(uint64_t));
		break;

	default:
		return false;
	}

	return true;
}

/**
 * Finds the memory region where initrd is stored, and udpates the fdt node
 * cursor to the node called "chosen".
 */
static bool find_initrd(struct fdt_node *n, struct boot_params *p)
{
	uint64_t begin;
	uint64_t end;

	if (!fdt_find_child(n, "chosen")) {
		dlog("Unable to find 'chosen'\n");
		return false;
	}

	if (!fdt_read_number(n, "linux,initrd-start", &begin)) {
		dlog("Unable to read linux,initrd-start\n");
		return false;
	}

	if (!fdt_read_number(n, "linux,initrd-end", &end)) {
		dlog("Unable to read linux,initrd-end\n");
		return false;
	}

	p->initrd_begin = pa_init(begin);
	p->initrd_end = pa_init(end);

	return true;
}

static void find_memory_range(const struct fdt_node *root,
			      struct boot_params *p)
{
	struct fdt_node n = *root;
	const char *name;
	uint64_t address_size;
	uint64_t size_size;
	uint64_t entry_size;

	/* Get the sizes of memory range addresses and sizes. */
	if (fdt_read_number(&n, "#address-cells", &address_size)) {
		address_size *= sizeof(uint32_t);
	} else {
		address_size = sizeof(uint32_t);
	}

	if (fdt_read_number(&n, "#size-cells", &size_size)) {
		size_size *= sizeof(uint32_t);
	} else {
		size_size = sizeof(uint32_t);
	}

	entry_size = address_size + size_size;

	/* Look for nodes with the device_type set to "memory". */
	if (!fdt_first_child(&n, &name)) {
		return;
	}

	do {
		const char *data;
		uint32_t size;
		if (!fdt_read_property(&n, "device_type", &data, &size) ||
		    size != sizeof("memory") ||
		    memcmp(data, "memory", sizeof("memory")) != 0 ||
		    !fdt_read_property(&n, "reg", &data, &size)) {
			continue;
		}

		/* Traverse all memory ranges within this node. */
		while (size >= entry_size) {
			uintpaddr_t addr = convert_number(data, address_size);
			size_t len =
				convert_number(data + address_size, size_size);

			if (len > pa_addr(p->mem_end) - pa_addr(p->mem_begin)) {
				/* Remember the largest range we've found. */
				p->mem_begin = pa_init(addr);
				p->mem_end = pa_init(addr + len);
			}

			size -= entry_size;
			data += entry_size;
		}
	} while (fdt_next_sibling(&n, &name));

	/* TODO: Check for "reserved-memory" nodes. */
}

bool fdt_get_boot_params(paddr_t fdt_addr, struct boot_params *p)
{
	struct fdt_header *fdt;
	struct fdt_node n;
	bool ret = false;

	/* Map the fdt header in. */
	if (!mm_identity_map(mm_va_from_pa(fdt_addr),
			     va_init(pa_addr(fdt_addr) + fdt_header_size()),
			     MM_MODE_R)) {
		dlog("Unable to map FDT header.\n");
		goto err_unmap_fdt_header;
	}

	fdt = mm_ptr_from_va(mm_va_from_pa(fdt_addr));

	if (!fdt_root_node(&n, fdt)) {
		dlog("FDT failed validation.\n");
		goto err_unmap_fdt_header;
	}

	/* Map the rest of the fdt in. */
	if (!mm_identity_map(mm_va_from_pa(fdt_addr),
			     va_init(pa_addr(fdt_addr) + fdt_total_size(fdt)),
			     MM_MODE_R)) {
		dlog("Unable to map full FDT.\n");
		goto err_unmap_fdt_header;
	}

	if (!fdt_find_child(&n, "")) {
		dlog("Unable to find FDT root node.\n");
		goto out_unmap_fdt;
	}

	p->mem_begin = pa_init(0);
	p->mem_end = pa_init(0);
	find_memory_range(&n, p);

	if (!find_initrd(&n, p)) {
		goto out_unmap_fdt;
	}

	p->kernel_arg = (size_t)fdt;
	ret = true;

out_unmap_fdt:
	mm_unmap(mm_va_from_pa(fdt_addr),
		 va_init(pa_addr(fdt_addr) + fdt_total_size(fdt)), 0);
	return ret;

err_unmap_fdt_header:
	mm_unmap(mm_va_from_pa(fdt_addr),
		 va_init(pa_addr(fdt_addr) + fdt_header_size()), 0);
	return false;
}

bool fdt_patch(paddr_t fdt_addr, struct boot_params_update *p)
{
	struct fdt_header *fdt;
	struct fdt_node n;
	bool ret = false;

	/* Map the fdt header in. */
	if (!mm_identity_map(mm_va_from_pa(fdt_addr),
			     va_init(pa_addr(fdt_addr) + fdt_header_size()),
			     MM_MODE_R)) {
		dlog("Unable to map FDT header.\n");
		return false;
	}

	fdt = mm_ptr_from_va(mm_va_from_pa(fdt_addr));

	if (!fdt_root_node(&n, fdt)) {
		dlog("FDT failed validation.\n");
		goto err_unmap_fdt_header;
	}

	/* Map the fdt (+ a page) in r/w mode in preparation for updating it. */
	if (!mm_identity_map(mm_va_from_pa(fdt_addr),
			     va_init(pa_addr(fdt_addr) + fdt_total_size(fdt) +
				     PAGE_SIZE),
			     MM_MODE_R | MM_MODE_W)) {
		dlog("Unable to map FDT in r/w mode.\n");
		goto err_unmap_fdt_header;
	}

	if (!fdt_find_child(&n, "")) {
		dlog("Unable to find FDT root node.\n");
		goto out_unmap_fdt;
	}

	if (!fdt_find_child(&n, "chosen")) {
		dlog("Unable to find 'chosen'\n");
		goto out_unmap_fdt;
	}

	/* Patch FDT to point to new ramdisk. */
	if (!fdt_write_number(&n, "linux,initrd-start",
			      pa_addr(p->initrd_begin))) {
		dlog("Unable to write linux,initrd-start\n");
		goto out_unmap_fdt;
	}

	if (!fdt_write_number(&n, "linux,initrd-end", pa_addr(p->initrd_end))) {
		dlog("Unable to write linux,initrd-end\n");
		goto out_unmap_fdt;
	}

	/* Patch fdt to reserve primary VM memory. */
	{
		size_t tmp = (size_t)&plat_update_boot_params;
		tmp = (tmp + 0x80000 - 1) & ~(0x80000 - 1);
		fdt_add_mem_reservation(fdt, tmp & ~0xfffff, 0x80000);
	}

	/* Patch fdt to reserve memory for secondary VMs. */
	fdt_add_mem_reservation(
		fdt, pa_addr(p->reserved_begin),
		pa_addr(p->reserved_end) - pa_addr(p->reserved_begin));

	ret = true;

out_unmap_fdt:
	/* Unmap FDT. */
	if (!mm_unmap(mm_va_from_pa(fdt_addr),
		      va_init(pa_addr(fdt_addr) + fdt_total_size(fdt) +
			      PAGE_SIZE),
		      0)) {
		dlog("Unable to unmap writable FDT.\n");
		return false;
	}
	return ret;

err_unmap_fdt_header:
	mm_unmap(mm_va_from_pa(fdt_addr),
		 va_init(pa_addr(fdt_addr) + fdt_header_size()), 0);
	return false;
}
