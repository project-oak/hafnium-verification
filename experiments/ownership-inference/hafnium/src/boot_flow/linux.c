/*
 * Copyright 2019 The Hafnium Authors.
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

#include "hf/check.h"
#include "hf/cpio.h"
#include "hf/dlog.h"
#include "hf/fdt_handler.h"
#include "hf/plat/boot_flow.h"
#include "hf/std.h"

/* Set by arch-specific boot-time hook. */
uintreg_t plat_boot_flow_fdt_addr;

/**
 * Returns the physical address of board FDT. This was passed to Hafnium in the
 * first kernel arg by the boot loader.
 */
paddr_t plat_boot_flow_get_fdt_addr(void)
{
	return pa_init((uintpaddr_t)plat_boot_flow_fdt_addr);
}

/**
 * When handing over to the primary, give it the same FDT address that was given
 * to Hafnium. The FDT may have been modified during Hafnium init.
 */
uintreg_t plat_boot_flow_get_kernel_arg(void)
{
	return plat_boot_flow_fdt_addr;
}

/**
 * Load initrd range from the board FDT.
 */
bool plat_boot_flow_get_initrd_range(const struct fdt_node *fdt_root,
				     paddr_t *begin, paddr_t *end)
{
	return fdt_find_initrd(fdt_root, begin, end);
}

bool plat_boot_flow_update(struct mm_stage1_locked stage1_locked,
			   const struct manifest *manifest,
			   struct boot_params_update *update,
			   struct memiter *cpio, struct mpool *ppool)
{
	struct memiter primary_initrd;
	const struct string *filename =
		&manifest->vm[HF_PRIMARY_VM_INDEX].primary.ramdisk_filename;

	if (string_is_empty(filename)) {
		memiter_init(&primary_initrd, NULL, 0);
	} else if (!cpio_get_file(cpio, filename, &primary_initrd)) {
		dlog("Unable to find primary initrd \"%s\".\n",
		     string_data(filename));
		return false;
	}

	update->initrd_begin = pa_from_va(va_from_ptr(primary_initrd.next));
	update->initrd_end = pa_from_va(va_from_ptr(primary_initrd.limit));

	return fdt_patch(stage1_locked, plat_boot_flow_get_fdt_addr(), update,
			 ppool);
}
