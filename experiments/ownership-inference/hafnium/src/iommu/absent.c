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

#include "hf/plat/iommu.h"

bool plat_iommu_init(const struct fdt_node *fdt_root,
		     struct mm_stage1_locked stage1_locked, struct mpool *ppool)
{
	(void)fdt_root;
	(void)stage1_locked;
	(void)ppool;

	return true;
}

void plat_iommu_identity_map(struct vm_locked vm_locked, paddr_t begin,
			     paddr_t end, uint32_t mode)
{
	(void)vm_locked;
	(void)begin;
	(void)end;
	(void)mode;
}
