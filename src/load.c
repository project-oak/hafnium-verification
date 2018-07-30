#include "load.h"

#include <stdbool.h>

#include "api.h"
#include "dlog.h"
#include "memiter.h"
#include "mm.h"
#include "std.h"
#include "vm.h"

/**
 * Copies data to an unmapped location by mapping it for write, copying the
 * data, then unmapping it.
 */
static bool copy_to_unmaped(paddr_t to, const void *from, size_t size)
{
	if (!mm_identity_map((vaddr_t)to, (vaddr_t)to + size, MM_MODE_W)) {
		return false;
	}

	memcpy((void *)to, from, size);

	mm_unmap(to, to + size, 0);

	return true;
}

/**
 * Moves the kernel of the primary VM to its final destination.
 */
static bool relocate(const char *from, size_t size)
{
	/* TODO: This is a hack. We must read the alignment from the binary. */
	extern char bin_end[];
	size_t tmp = (size_t)&bin_end[0];
	paddr_t dest = (tmp + 0x80000 - 1) & ~(0x80000 - 1);
	dlog("bin_end is at %p, copying to %p\n", &bin_end[0], dest);
	return copy_to_unmaped(dest, from, size);
}

/**
 * Looks for a file in the given cpio archive. The filename is not
 * null-terminated, so we use a memory iterator to represent it. The file, if
 * found, is returned in the "it" argument.
 */
static bool memiter_find_file(const struct memiter *cpio,
			      const struct memiter *filename,
			      struct memiter *it)
{
	const char *fname;
	const void *fcontents;
	size_t fsize;
	struct memiter iter = *cpio;

	while (cpio_next(&iter, &fname, &fcontents, &fsize)) {
		if (memiter_iseq(filename, fname)) {
			memiter_init(it, fcontents, fsize);
			return true;
		}
	}

	return false;
}

/**
 * Looks for a file in the given cpio archive. The file, if found, is returned
 * in the "it" argument.
 */
static bool find_file(const struct memiter *cpio, const char *name,
		      struct memiter *it)
{
	const char *fname;
	const void *fcontents;
	size_t fsize;
	struct memiter iter = *cpio;

	while (cpio_next(&iter, &fname, &fcontents, &fsize)) {
		if (!strcmp(fname, name)) {
			memiter_init(it, fcontents, fsize);
			return true;
		}
	}

	return false;
}

/**
 * Loads the primary VM.
 */
bool load_primary(const struct memiter *cpio, size_t kernel_arg,
		  struct memiter *initrd)
{
	struct memiter it;

	if (!find_file(cpio, "vmlinuz", &it)) {
		dlog("Unable to find vmlinuz\n");
		return false;
	}

	if (!relocate(it.next, it.limit - it.next)) {
		dlog("Unable to relocate kernel for primary vm.\n");
		return false;
	}

	if (!find_file(cpio, "initrd.img", initrd)) {
		dlog("Unable to find initrd.img\n");
		return false;
	}

	{
		size_t tmp = (size_t)&load_primary;
		tmp = (tmp + 0x80000 - 1) & ~(0x80000 - 1);
		if (!vm_init(&primary_vm, 0, MAX_CPUS)) {
			dlog("Unable to initialise primary vm\n");
			return false;
		}

		/* Map the 1TB of memory. */
		/* TODO: We should do a whitelist rather than a blacklist. */
		if (!mm_ptable_identity_map(&primary_vm.ptable, 0,
					    1024ull * 1024 * 1024 * 1024,
					    MM_MODE_R | MM_MODE_W | MM_MODE_X |
						    MM_MODE_NOINVALIDATE)) {
			dlog("Unable to initialise memory for primary vm\n");
			return false;
		}

		if (!mm_ptable_unmap_hypervisor(&primary_vm.ptable,
						MM_MODE_NOINVALIDATE)) {
			dlog("Unable to unmap hypervisor from primary vm\n");
			return false;
		}

		vm_start_vcpu(&primary_vm, 0, tmp, kernel_arg, true);
	}

	return true;
}

/**
 * Loads all secondary VMs in the given memory range. "mem_end" is updated to
 * reflect the fact that some of the memory isn't available to the primary VM
 * anymore.
 */
bool load_secondary(const struct memiter *cpio, uint64_t mem_begin,
		    uint64_t *mem_end)
{
	struct memiter it;
	struct memiter str;
	uint64_t mem;
	uint64_t cpu;
	uint32_t count;

	if (!find_file(cpio, "vms.txt", &it)) {
		dlog("vms.txt is missing\n");
		return true;
	}

	/* Round the last address down to the page size. */
	*mem_end &= ~(PAGE_SIZE - 1);

	for (count = 0;
	     memiter_parse_uint(&it, &mem) && memiter_parse_uint(&it, &cpu) &&
	     memiter_parse_str(&it, &str) && count < MAX_VMS;
	     count++) {
		struct memiter kernel;

		if (!memiter_find_file(cpio, &str, &kernel)) {
			dlog("Unable to load kernel for vm %u\n", count);
			continue;
		}

		/* Round up to page size. */
		mem = (mem + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);
		if (mem > *mem_end - mem_begin) {
			dlog("Not enough memory for vm %u (%u bytes)\n", count,
			     mem);
			continue;
		}

		if (mem < kernel.limit - kernel.next) {
			dlog("Kernel is larger than available memory for vm "
			     "%u\n",
			     count);
			continue;
		}

		*mem_end -= mem;
		if (!copy_to_unmaped(*mem_end, kernel.next,
				     kernel.limit - kernel.next)) {
			dlog("Unable to copy kernel for vm %u\n", count);
			continue;
		}

		if (!vm_init(secondary_vm + count, count + 1, cpu)) {
			dlog("Unable to initialise vm %u\n", count);
			continue;
		}

		/* TODO: Remove this. */
		/* Grant VM access to uart. */
		mm_ptable_identity_map_page(&secondary_vm[count].ptable,
					    PL011_BASE,
					    MM_MODE_R | MM_MODE_W | MM_MODE_D |
						    MM_MODE_NOINVALIDATE);

		/* Grant the VM access to the memory. */
		if (!mm_ptable_identity_map(&secondary_vm[count].ptable,
					    *mem_end, *mem_end + mem,
					    MM_MODE_R | MM_MODE_W | MM_MODE_X |
						    MM_MODE_NOINVALIDATE)) {
			dlog("Unable to initialise memory for vm %u\n", count);
			continue;
		}

		/* Deny the primary VM access to this memory. */
		if (!mm_ptable_unmap(&primary_vm.ptable, *mem_end,
				     *mem_end + mem, MM_MODE_NOINVALIDATE)) {
			dlog("Unable to unmap secondary VM from primary VM\n");
			return false;
		}

		dlog("Loaded VM%u with %u vcpus, entry at 0x%x\n", count, cpu,
		     *mem_end);

		vm_start_vcpu(secondary_vm + count, 0, *mem_end, 0, false);
	}

	secondary_vm_count = count;

	return true;
}
