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

#include "hf/layout.h"
#include "hf/plat/boot_flow.h"

/**
 * FDT was compiled into Hafnium. Return physical address of the `.plat.fdt`
 * section of Hafnium image.
 */
paddr_t plat_boot_flow_get_fdt_addr(void)
{
	return layout_fdt_begin();
}

/**
 * Android boot flow does not use kernel arguments. Pass zero.
 */
uintreg_t plat_boot_flow_get_kernel_arg(void)
{
	return 0;
}

/**
 * Initrd was compiled into Hafnium. Return range of the '.plat.initrd' section.
 */
bool plat_boot_flow_get_initrd_range(const struct fdt_node *fdt_root,
				     paddr_t *begin, paddr_t *end)
{
	(void)fdt_root;

	*begin = layout_initrd_begin();
	*end = layout_initrd_end();
	return true;
}

/**
 * Android boot flow does not change based on the updates.
 */
bool plat_boot_flow_update(struct mm_stage1_locked stage1_locked,
			   const struct manifest *manifest,
			   struct boot_params_update *p, struct memiter *cpio,
			   struct mpool *ppool)
{
	(void)stage1_locked;
	(void)manifest;
	(void)p;
	(void)cpio;
	(void)ppool;

	return true;
}
