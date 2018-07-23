#include <stdalign.h>
#include <stddef.h>
#include <stdnoreturn.h>

#include "alloc.h"
#include "api.h"
#include "boot_params.h"
#include "cpio.h"
#include "cpu.h"
#include "dlog.h"
#include "load.h"
#include "mm.h"
#include "std.h"
#include "vm.h"

char ptable_buf[PAGE_SIZE * 20];

/**
 * Blocks the hypervisor.
 *
 * TODO: Determine if we want to omit strings on non-debug builds.
 */
noreturn void panic(const char *fmt, ...)
{
	va_list args;

	/* TODO: Block all CPUs. */

	dlog("Panic: ");

	va_start(args, fmt);
	vdlog(fmt, args);
	va_end(args);

	dlog("\n");

	for (;;) {
	}
}

/**
 * Performs one-time initialisation of the hypervisor.
 */
static void one_time_init(void)
{
	struct boot_params params;
	struct boot_params_update update;
	uint64_t new_mem_end;
	struct memiter primary_initrd;
	struct memiter cpio;

	dlog("Initialising hafnium\n");

	cpu_module_init();
	halloc_init((size_t)ptable_buf, sizeof(ptable_buf));

	if (!mm_init()) {
		panic("mm_init failed");
	}

	if (!plat_get_boot_params(&params)) {
		panic("unable to retrieve boot params");
	}

	dlog("Memory range:  0x%x - 0x%x\n", params.mem_begin,
	     params.mem_end - 1);
	dlog("Ramdisk range: 0x%x - 0x%x\n", params.initrd_begin,
	     params.initrd_end - 1);

	/* Map initrd in, and initialise cpio parser. */
	if (!mm_map(params.initrd_begin, params.initrd_end, params.initrd_begin,
		    MM_MODE_R)) {
		panic("unable to map initrd in");
	}

	memiter_init(&cpio, (void *)params.initrd_begin,
		     params.initrd_end - params.initrd_begin);

	/* Load all VMs. */
	new_mem_end = params.mem_end;
	load_secondary(&cpio, params.mem_begin, &new_mem_end);
	if (!load_primary(&cpio, params.kernel_arg, &primary_initrd)) {
		panic("unable to load primary VM");
	}

	/* Prepare to run by updating bootparams as seens by primary VM. */
	update.initrd_begin = (paddr_t)primary_initrd.next;
	update.initrd_end = (paddr_t)primary_initrd.limit;
	update.reserved_begin = new_mem_end;
	update.reserved_end = params.mem_end - new_mem_end;
	if (!plat_update_boot_params(&update)) {
		panic("plat_update_boot_params failed");
	}

	mm_defrag();

	dlog("Hafnium initialisation completed\n");
}

/**
 * The entry point of CPUs when they are turned on. It is supposed to initialise
 * all state and return the first vCPU to run.
 */
struct vcpu *cpu_main(void)
{
	struct cpu *c = cpu();

	/*
	 * Do global one-time initialisation just once. We avoid using atomics
	 * by only touching the variable from cpu 0.
	 */
	static volatile bool inited = false;
	if (cpu_index(c) == 0 && !inited) {
		inited = true;
		one_time_init();
	}

	dlog("Starting up cpu %d\n", cpu_index(c));

	return primary_vm.vcpus + cpu_index(c);
}
