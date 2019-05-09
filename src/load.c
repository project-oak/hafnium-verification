/*
 * Copyright 2018 The Hafnium Authors.
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

#include "hf/load.h"

#include <stdbool.h>

#include "hf/api.h"
#include "hf/boot_params.h"
#include "hf/dlog.h"
#include "hf/layout.h"
#include "hf/memiter.h"
#include "hf/mm.h"
#include "hf/plat/console.h"
#include "hf/static_assert.h"
#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

/**
 * Copies data to an unmapped location by mapping it for write, copying the
 * data, then unmapping it.
 *
 * The data is written so that it is available to all cores with the cache
 * disabled. When switching to the partitions, the caching is initially disabled
 * so the data must be available without the cache.
 */
static bool copy_to_unmapped(struct mm_stage1_locked stage1_locked, paddr_t to,
			     const void *from, size_t size, struct mpool *ppool)
{
	paddr_t to_end = pa_add(to, size);
	void *ptr;

	ptr = mm_identity_map(stage1_locked, to, to_end, MM_MODE_W, ppool);
	if (!ptr) {
		return false;
	}

	memcpy_s(ptr, size, from, size);
	arch_mm_write_back_dcache(ptr, size);

	mm_unmap(stage1_locked, to, to_end, ppool);

	return true;
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
bool load_primary(struct mm_stage1_locked stage1_locked,
		  const struct memiter *cpio, uintreg_t kernel_arg,
		  struct memiter *initrd, struct mpool *ppool)
{
	struct memiter it;
	paddr_t primary_begin = layout_primary_begin();

	if (!find_file(cpio, "vmlinuz", &it)) {
		dlog("Unable to find vmlinuz\n");
		return false;
	}

	dlog("Copying primary to %p\n", pa_addr(primary_begin));
	if (!copy_to_unmapped(stage1_locked, primary_begin, it.next,
			      it.limit - it.next, ppool)) {
		dlog("Unable to relocate kernel for primary vm.\n");
		return false;
	}

	if (!find_file(cpio, "initrd.img", initrd)) {
		dlog("Unable to find initrd.img\n");
		return false;
	}

	{
		struct vm *vm;
		struct vcpu_locked vcpu_locked;

		if (!vm_init(MAX_CPUS, ppool, &vm)) {
			dlog("Unable to initialise primary vm\n");
			return false;
		}

		if (vm->id != HF_PRIMARY_VM_ID) {
			dlog("Primary vm was not given correct id\n");
			return false;
		}

		/* Map the 1TB of memory. */
		/* TODO: We should do a whitelist rather than a blacklist. */
		if (!mm_vm_identity_map(
			    &vm->ptable, pa_init(0),
			    pa_init(UINT64_C(1024) * 1024 * 1024 * 1024),
			    MM_MODE_R | MM_MODE_W | MM_MODE_X, NULL, ppool)) {
			dlog("Unable to initialise memory for primary vm\n");
			return false;
		}

		if (!mm_vm_unmap_hypervisor(&vm->ptable, ppool)) {
			dlog("Unable to unmap hypervisor from primary vm\n");
			return false;
		}

		vcpu_locked = vcpu_lock(vm_get_vcpu(vm, 0));
		vcpu_on(vcpu_locked, ipa_from_pa(primary_begin), kernel_arg);
		vcpu_unlock(&vcpu_locked);
	}

	return true;
}

/**
 * Try to find a memory range of the given size within the given ranges, and
 * remove it from them. Return true on success, or false if no large enough
 * contiguous range is found.
 */
static bool carve_out_mem_range(struct mem_range *mem_ranges,
				size_t mem_ranges_count, uint64_t size_to_find,
				paddr_t *found_begin, paddr_t *found_end)
{
	size_t i;

	/*
	 * TODO(b/116191358): Consider being cleverer about how we pack VMs
	 * together, with a non-greedy algorithm.
	 */
	for (i = 0; i < mem_ranges_count; ++i) {
		if (size_to_find <=
		    pa_difference(mem_ranges[i].begin, mem_ranges[i].end)) {
			/*
			 * This range is big enough, take some of it from the
			 * end and reduce its size accordingly.
			 */
			*found_end = mem_ranges[i].end;
			*found_begin = pa_init(pa_addr(mem_ranges[i].end) -
					       size_to_find);
			mem_ranges[i].end = *found_begin;
			return true;
		}
	}
	return false;
}

/**
 * Given arrays of memory ranges before and after memory was removed for
 * secondary VMs, add the difference to the reserved ranges of the given update.
 * Return true on success, or false if there would be more than MAX_MEM_RANGES
 * reserved ranges after adding the new ones.
 * `before` and `after` must be arrays of exactly `mem_ranges_count` elements.
 */
static bool update_reserved_ranges(struct boot_params_update *update,
				   const struct mem_range *before,
				   const struct mem_range *after,
				   size_t mem_ranges_count)
{
	size_t i;

	for (i = 0; i < mem_ranges_count; ++i) {
		if (pa_addr(after[i].begin) > pa_addr(before[i].begin)) {
			if (update->reserved_ranges_count >= MAX_MEM_RANGES) {
				dlog("Too many reserved ranges after loading "
				     "secondary VMs.\n");
				return false;
			}
			update->reserved_ranges[update->reserved_ranges_count]
				.begin = before[i].begin;
			update->reserved_ranges[update->reserved_ranges_count]
				.end = after[i].begin;
			update->reserved_ranges_count++;
		}
		if (pa_addr(after[i].end) < pa_addr(before[i].end)) {
			if (update->reserved_ranges_count >= MAX_MEM_RANGES) {
				dlog("Too many reserved ranges after loading "
				     "secondary VMs.\n");
				return false;
			}
			update->reserved_ranges[update->reserved_ranges_count]
				.begin = after[i].end;
			update->reserved_ranges[update->reserved_ranges_count]
				.end = before[i].end;
			update->reserved_ranges_count++;
		}
	}

	return true;
}

/**
 * Loads all secondary VMs into the memory ranges from the given params.
 * Memory reserved for the VMs is added to the `reserved_ranges` of `update`.
 */
bool load_secondary(struct mm_stage1_locked stage1_locked,
		    const struct memiter *cpio,
		    const struct boot_params *params,
		    struct boot_params_update *update, struct mpool *ppool)
{
	struct vm *primary;
	struct memiter it;
	struct memiter name;
	uint64_t mem;
	uint64_t cpu;
	struct mem_range mem_ranges_available[MAX_MEM_RANGES];
	size_t i;

	static_assert(
		sizeof(mem_ranges_available) == sizeof(params->mem_ranges),
		"mem_range arrays must be the same size for memcpy.");
	static_assert(sizeof(mem_ranges_available) < 500,
		      "This will use too much stack, either make "
		      "MAX_MEM_RANGES smaller or change this.");
	memcpy_s(mem_ranges_available, sizeof(mem_ranges_available),
		 params->mem_ranges, sizeof(params->mem_ranges));

	primary = vm_find(HF_PRIMARY_VM_ID);

	if (!find_file(cpio, "vms.txt", &it)) {
		dlog("vms.txt is missing\n");
		return true;
	}

	/* Round the last addresses down to the page size. */
	for (i = 0; i < params->mem_ranges_count; ++i) {
		mem_ranges_available[i].end = pa_init(align_down(
			pa_addr(mem_ranges_available[i].end), PAGE_SIZE));
	}

	while (memiter_parse_uint(&it, &mem) && memiter_parse_uint(&it, &cpu) &&
	       memiter_parse_str(&it, &name)) {
		struct memiter kernel;
		paddr_t secondary_mem_begin;
		paddr_t secondary_mem_end;
		ipaddr_t secondary_entry;
		const char *p;
		struct vm *vm;
		struct vcpu *vcpu;

		dlog("Loading ");
		for (p = name.next; p != name.limit; ++p) {
			dlog("%c", *p);
		}
		dlog("\n");

		if (!memiter_find_file(cpio, &name, &kernel)) {
			dlog("Unable to load kernel\n");
			continue;
		}

		/* Round up to page size. */
		mem = (mem + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);

		if (mem < kernel.limit - kernel.next) {
			dlog("Kernel is larger than available memory\n");
			continue;
		}

		if (!carve_out_mem_range(
			    mem_ranges_available, params->mem_ranges_count, mem,
			    &secondary_mem_begin, &secondary_mem_end)) {
			dlog("Not enough memory (%u bytes)\n", mem);
			continue;
		}

		if (!copy_to_unmapped(stage1_locked, secondary_mem_begin,
				      kernel.next, kernel.limit - kernel.next,
				      ppool)) {
			dlog("Unable to copy kernel\n");
			continue;
		}

		if (!vm_init(cpu, ppool, &vm)) {
			dlog("Unable to initialise VM\n");
			continue;
		}

		/* Grant the VM access to the memory. */
		if (!mm_vm_identity_map(&vm->ptable, secondary_mem_begin,
					secondary_mem_end,
					MM_MODE_R | MM_MODE_W | MM_MODE_X,
					&secondary_entry, ppool)) {
			dlog("Unable to initialise memory\n");
			continue;
		}

		/* Deny the primary VM access to this memory. */
		if (!mm_vm_unmap(&primary->ptable, secondary_mem_begin,
				 secondary_mem_end, ppool)) {
			dlog("Unable to unmap secondary VM from primary VM\n");
			return false;
		}

		dlog("Loaded with %u vcpus, entry at 0x%x\n", cpu,
		     pa_addr(secondary_mem_begin));

		vcpu = vm_get_vcpu(vm, 0);
		vcpu_secondary_reset_and_start(
			vcpu, secondary_entry,
			pa_difference(secondary_mem_begin, secondary_mem_end));
	}

	/*
	 * Add newly reserved areas to update params by looking at the
	 * difference between the available ranges from the original params and
	 * the updated mem_ranges_available. We assume that the number and order
	 * of available ranges is the same, i.e. we don't remove any ranges
	 * above only make them smaller.
	 */
	return update_reserved_ranges(update, params->mem_ranges,
				      mem_ranges_available,
				      params->mem_ranges_count);
}
