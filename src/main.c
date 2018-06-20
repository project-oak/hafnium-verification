#include <stdalign.h>
#include <stdatomic.h>
#include <stddef.h>

#include "cpio.h"
#include "cpu.h"
#include "dlog.h"
#include "fdt.h"
#include "irq.h"
#include "std.h"
#include "timer.h"
#include "vm.h"

void *fdt;

/* The stack to be used by the CPUs. */
alignas(2 * sizeof(size_t)) char callstacks[STACK_SIZE * MAX_CPUS];

/* State of all supported CPUs. The stack of the first one is initialized. */
struct cpu cpus[MAX_CPUS] = {
	{
		.cpu_on_count = 1,
		.stack_bottom = callstacks + STACK_SIZE,
	},
};

bool fdt_find_node(struct fdt_node *node, const char *path)
{
	if (!fdt_find_child(node, ""))
		return false;

	while (*path) {
		if (!fdt_find_child(node, path))
			return false;
		path += strlen(path);
	}

	return true;
}

bool fdt_read_number(struct fdt_node *node, const char *name, uint64_t *value)
{
	const char *data;
	uint32_t size;
	union {
		volatile uint64_t v;
		char a[8];
	} t;

	if (!fdt_read_property(node, name, &data, &size))
		return false;

	switch (size) {
	case sizeof(uint32_t):
		*value = ntohl(*(uint32_t *)data);
		break;

	case sizeof(uint64_t):
		memcpy(t.a, data, sizeof(uint64_t));
		*value = ntohll(t.v);
		break;

	default:
		return false;
	}

	return true;
}

bool fdt_write_number(struct fdt_node *node, const char *name, uint64_t value)
{
	const char *data;
	uint32_t size;
	union {
		volatile uint64_t v;
		char a[8];
	} t;

	if (!fdt_read_property(node, name, &data, &size))
		return false;

	switch (size) {
	case sizeof(uint32_t):
		*(uint32_t *)data = ntohl(value);
		break;

	case sizeof(uint64_t):
		t.v = ntohll(value);
		memcpy((void *)data, t.a, sizeof(uint64_t));
		break;

	default:
		return false;
	}

	return true;
}

static void relocate(const char *from, size_t size)
{
	extern char bin_end[];
	size_t tmp = (size_t)&bin_end[0];
	char *dest = (char *)((tmp + 0x80000 - 1) & ~(0x80000 - 1));
	dlog("bin_end is at %p, copying to %p\n", &bin_end[0], dest);
	memcpy(dest, from, size);
}

/* TODO: Remove this. */
struct vm vm0;

static void one_time_init(void)
{
	size_t i;

	dlog("Initializing hafnium\n");

	/*
	 * TODO: Re-enable this.
	irq_init();
	timer_init();
	*/

	/* Initialize all CPUs. */
	for (i = 0; i < MAX_CPUS; i++) {
		struct cpu *c = cpus + i;
		cpu_init(c);
		c->id = i; /* TODO: Initialize ID. */
		c->stack_bottom = callstacks + STACK_SIZE * (i + 1);
	}

	/* TODO: Code below this point should be removed from this function. */
	/* TODO: Remove this. */

	do {
		struct fdt_node n;

		fdt_root_node(&n, fdt);
		if (!fdt_find_node(&n, "chosen\0")) {
			dlog("Unable to find 'chosen'\n");
			break;
		}

		uint64_t begin;
		uint64_t end;

		if (!fdt_read_number(&n, "linux,initrd-start", &begin)) {
			dlog("Unable to read linux,initrd-start\n");
			break;
		}

		if (!fdt_read_number(&n, "linux,initrd-end", &end)) {
			dlog("Unable to read linux,initrd-end\n");
			break;
		}

		dlog("Ramdisk: from %x to %x\n", begin, end);

		struct cpio c;
		struct cpio_iter iter;
		cpio_init(&c, (void *)begin, end - begin);
		cpio_init_iter(&c, &iter);

		const char *name;
		const void *fcontents;
		size_t ramdisk = 0;
		size_t ramdisk_end = 0;
		size_t fsize;
		while (cpio_next(&iter, &name, &fcontents, &fsize)) {
			dlog("File: %s, size=%u\n", name, fsize);
			if (!strcmp(name, "vm/vmlinuz")) {
				relocate(fcontents, fsize);
				continue;
			}

			if (!strcmp(name, "vm/initrd.img")) {
				dlog("Found vm/ramdisk @ %p, %u bytes\n", fcontents, fsize);
				ramdisk = (size_t)fcontents;
				ramdisk_end = ramdisk + fsize;
				continue;
			}
		}

		dlog("Ramdisk; %p\n", ramdisk);

		/* Patch FDT to point to new ramdisk. */
		if (!fdt_write_number(&n, "linux,initrd-start", ramdisk)) {
			dlog("Unable to write linux,initrd-start\n");
			break;
		}

		if (!fdt_write_number(&n, "linux,initrd-end", ramdisk_end)) {
			dlog("Unable to write linux,initrd-end\n");
			break;
		}

		/*
		 * Patch fdt to point remove memory.
		 */
		{
			size_t tmp = (size_t)&relocate;
			tmp = (tmp + 0x80000 - 1) & ~(0x80000 - 1);


			fdt_add_mem_reservation(fdt, tmp & ~0xfffff, 0x80000);
			vm_init(&vm0, cpus);
			vm_start_vcpu(&vm0, 0, tmp, (size_t)fdt);
		}
	} while (0);
}

/*
 * The entry point of CPUs when they are turned on. It is supposed to initialise
 * all state and return; the caller will ensure that the next vcpu runs.
 */
void cpu_main(void)
{
	/* Do global one-time initialization just once. */
	static atomic_flag inited = ATOMIC_FLAG_INIT;
	if (!atomic_flag_test_and_set_explicit(&inited, memory_order_acq_rel))
		one_time_init();

	dlog("Starting up cpu %d\n", cpu() - cpus);

	/* Do per-cpu initialization. */
	/* TODO: What to do here? */
	/*
	irq_init_percpu();
	timer_init_percpu();
	*/
}
