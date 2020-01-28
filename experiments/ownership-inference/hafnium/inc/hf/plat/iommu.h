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

#pragma once

#include "hf/addr.h"
#include "hf/fdt.h"
#include "hf/vm.h"

/**
 * Initializes the platform IOMMU driver. The root node of the FDT is provided
 * so that the driver can read from it. This can be used to map IOMMU devices
 * into the hypervisor's address space so they are accessible by the driver.
 */
bool plat_iommu_init(const struct fdt_node *fdt_root,
		     struct mm_stage1_locked stage1_locked,
		     struct mpool *ppool);

/**
 * Maps the address range with the given mode for the given VM in the IOMMU.
 *
 * Assumes the identity map cannot fail. This may not always be true and if it
 * isn't it will require careful thought on how to safely handle error cases
 * when intermingled with MMU updates but it gives a starting point for drivers
 * until those problems are understood.
 *
 * The modes are the same as the memory management modes but it is only required
 * that read and write modes are enforced by the IOMMU driver.
 */
void plat_iommu_identity_map(struct vm_locked vm_locked, paddr_t begin,
			     paddr_t end, uint32_t mode);
