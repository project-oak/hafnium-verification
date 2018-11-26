/*
 * Copyright 2018 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "hf/fdt_handler.h"

#include "hf/boot_params.h"
#include "hf/cpu.h"
#include "hf/dlog.h"
#include "hf/fdt.h"
#include "hf/layout.h"
#include "hf/mm.h"
#include "hf/std.h"

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
 * Finds the memory region where initrd is stored, and updates the fdt node
 * cursor to the node called "chosen".
 */
bool fdt_find_initrd(struct fdt_node *n, paddr_t *begin, paddr_t *end)
{
	uint64_t initrd_begin;
	uint64_t initrd_end;

	if (!fdt_find_child(n, "chosen")) {
		dlog("Unable to find 'chosen'\n");
		return false;
	}

	if (!fdt_read_number(n, "linux,initrd-start", &initrd_begin)) {
		dlog("Unable to read linux,initrd-start\n");
		return false;
	}

	if (!fdt_read_number(n, "linux,initrd-end", &initrd_end)) {
		dlog("Unable to read linux,initrd-end\n");
		return false;
	}

	*begin = pa_init(initrd_begin);
	*end = pa_init(initrd_end);

	return true;
}

void fdt_find_cpus(const struct fdt_node *root, uint64_t *cpu_ids,
		   size_t *cpu_count)
{
	struct fdt_node n = *root;
	const char *name;
	uint64_t address_size;

	*cpu_count = 0;

	if (!fdt_find_child(&n, "cpus")) {
		dlog("Unable to find 'cpus'\n");
		return;
	}

	if (fdt_read_number(&n, "#address-cells", &address_size)) {
		address_size *= sizeof(uint32_t);
	} else {
		address_size = sizeof(uint32_t);
	}

	if (!fdt_first_child(&n, &name)) {
		return;
	}

	do {
		const char *data;
		uint32_t size;

		if (!fdt_read_property(&n, "device_type", &data, &size) ||
		    size != sizeof("cpu") ||
		    memcmp(data, "cpu", sizeof("cpu")) != 0 ||
		    !fdt_read_property(&n, "reg", &data, &size)) {
			continue;
		}

		/* Get all entries for this CPU. */
		while (size >= address_size) {
			if (*cpu_count >= MAX_CPUS) {
				dlog("Found more than %d CPUs\n", MAX_CPUS);
				return;
			}

			cpu_ids[(*cpu_count)++] =
				convert_number(data, address_size);

			size -= address_size;
			data += address_size;
		}
	} while (fdt_next_sibling(&n, &name));
}

void fdt_find_memory_ranges(const struct fdt_node *root, struct boot_params *p)
{
	struct fdt_node n = *root;
	const char *name;
	uint64_t address_size;
	uint64_t size_size;
	uint64_t entry_size;
	size_t mem_range_index = 0;

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

			if (mem_range_index < MAX_MEM_RANGES) {
				p->mem_ranges[mem_range_index].begin =
					pa_init(addr);
				p->mem_ranges[mem_range_index].end =
					pa_init(addr + len);
				++mem_range_index;
			} else {
				dlog("Found memory range %u in FDT but only "
				     "%u supported, ignoring additional range "
				     "of size %u.\n",
				     mem_range_index, MAX_MEM_RANGES, len);
			}

			size -= entry_size;
			data += entry_size;
		}
	} while (fdt_next_sibling(&n, &name));
	p->mem_ranges_count = mem_range_index;

	/* TODO: Check for "reserved-memory" nodes. */
}

struct fdt_header *fdt_map(paddr_t fdt_addr, struct fdt_node *n,
			   struct mpool *ppool)
{
	struct fdt_header *fdt;

	/* Map the fdt header in. */
	fdt = mm_identity_map(fdt_addr, pa_add(fdt_addr, fdt_header_size()),
			      MM_MODE_R, ppool);
	if (!fdt) {
		dlog("Unable to map FDT header.\n");
		return NULL;
	}

	if (!fdt_root_node(n, fdt)) {
		dlog("FDT failed validation.\n");
		goto fail;
	}

	/* Map the rest of the fdt in. */
	fdt = mm_identity_map(fdt_addr, pa_add(fdt_addr, fdt_total_size(fdt)),
			      MM_MODE_R, ppool);
	if (!fdt) {
		dlog("Unable to map full FDT.\n");
		goto fail;
	}

	return fdt;

fail:
	mm_unmap(fdt_addr, pa_add(fdt_addr, fdt_header_size()), ppool);
	return NULL;
}

bool fdt_unmap(struct fdt_header *fdt, struct mpool *ppool)
{
	paddr_t fdt_addr = pa_from_va(va_from_ptr(fdt));

	return mm_unmap(fdt_addr, pa_add(fdt_addr, fdt_total_size(fdt)), ppool);
}

bool fdt_patch(paddr_t fdt_addr, struct boot_params_update *p,
	       struct mpool *ppool)
{
	struct fdt_header *fdt;
	struct fdt_node n;
	bool ret = false;
	size_t i;

	/* Map the fdt header in. */
	fdt = mm_identity_map(fdt_addr, pa_add(fdt_addr, fdt_header_size()),
			      MM_MODE_R, ppool);
	if (!fdt) {
		dlog("Unable to map FDT header.\n");
		return false;
	}

	if (!fdt_root_node(&n, fdt)) {
		dlog("FDT failed validation.\n");
		goto err_unmap_fdt_header;
	}

	/* Map the fdt (+ a page) in r/w mode in preparation for updating it. */
	fdt = mm_identity_map(fdt_addr,
			      pa_add(fdt_addr, fdt_total_size(fdt) + PAGE_SIZE),
			      MM_MODE_R | MM_MODE_W, ppool);
	if (!fdt) {
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
	fdt_add_mem_reservation(
		fdt, align_down(pa_addr(layout_primary_begin()), 0x100000),
		0x80000);

	/* Patch fdt to reserve memory for secondary VMs. */
	for (i = 0; i < p->reserved_ranges_count; ++i) {
		fdt_add_mem_reservation(
			fdt, pa_addr(p->reserved_ranges[i].begin),
			pa_addr(p->reserved_ranges[i].end) -
				pa_addr(p->reserved_ranges[i].begin));
	}

	ret = true;

out_unmap_fdt:
	/* Unmap FDT. */
	if (!mm_unmap(fdt_addr,
		      pa_add(fdt_addr, fdt_total_size(fdt) + PAGE_SIZE),
		      ppool)) {
		dlog("Unable to unmap writable FDT.\n");
		return false;
	}
	return ret;

err_unmap_fdt_header:
	mm_unmap(fdt_addr, pa_add(fdt_addr, fdt_header_size()), ppool);
	return false;
}
