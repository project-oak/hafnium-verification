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

#include "hf/boot_params.h"
#include "hf/dlog.h"
#include "hf/fdt_handler.h"
#include "hf/layout.h"

/**
 * Default implementation assumes the FDT has been linked into the image.
 *
 * This can be overridden e.g. to provide a fixed address or an address passed
 * by the loader.
 */
#pragma weak plat_get_fdt_addr
paddr_t plat_get_fdt_addr(void)
{
	return layout_fdt_begin();
}

/**
 * Default implementation assumes the initrd has been linked into the image.
 *
 * This can be overridden e.g. to provide a fixed address or an address passed
 * by the loader.
 */
#pragma weak plat_get_initrd_range
void plat_get_initrd_range(paddr_t *begin, paddr_t *end, struct mpool *ppool)
{
	(void)ppool;

	*begin = layout_initrd_begin();
	*end = layout_initrd_end();
}

/**
 * Default implementation assumes the FDT address is passed to the kernel.
 *
 * TODO: make this part of the VM configuration as secondary VMs will also need
 * to take arguments.
 */
#pragma weak plat_get_kernel_arg
uintreg_t plat_get_kernel_arg(void)
{
	return (uintreg_t)pa_addr(plat_get_fdt_addr());
}

/**
 * Default implementation extracts the boot parameters from the FDT but the
 * initrd is provided separately.
 */
#pragma weak plat_get_boot_params
bool plat_get_boot_params(struct boot_params *p, struct mpool *ppool)
{
	struct fdt_header *fdt;
	struct fdt_node n;
	bool ret = false;

	plat_get_initrd_range(&p->initrd_begin, &p->initrd_end, ppool);
	p->kernel_arg = plat_get_kernel_arg();

	/* Get the memory map from the FDT. */
	fdt = fdt_map(plat_get_fdt_addr(), &n, ppool);
	if (!fdt) {
		return false;
	}

	if (!fdt_find_child(&n, "")) {
		dlog("Unable to find FDT root node.\n");
		goto out_unmap_fdt;
	}

	p->mem_ranges_count = 0;
	fdt_find_memory_ranges(&n, p);

	ret = true;

out_unmap_fdt:
	if (!fdt_unmap(fdt, ppool)) {
		dlog("Unable to unmap fdt.");
		return false;
	}

	return ret;
}

/**
 * Default implementation updates the FDT which is the argument passed to the
 * primary VM's kernel.
 *
 * TODO: in future, each VM will declare whether it expects an argument passed
 * and that will be static data e.g. it will provide its own FDT so there will
 * be no FDT modification. This is done because each VM has a very different
 * view of the system and we don't want to force VMs to require loader code when
 * another loader can load the data for it.
 */
#pragma weak plat_update_boot_params
bool plat_update_boot_params(struct boot_params_update *p, struct mpool *ppool)
{
	return fdt_patch(plat_get_fdt_addr(), p, ppool);
}
