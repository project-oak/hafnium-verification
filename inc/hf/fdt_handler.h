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

#pragma once

#include "hf/boot_params.h"
#include "hf/fdt.h"
#include "hf/mm.h"

struct fdt_header *fdt_map(paddr_t fdt_addr, struct fdt_node *n);
bool fdt_unmap(struct fdt_header *fdt);
void fdt_find_memory_ranges(const struct fdt_node *root, struct boot_params *p);
bool fdt_find_initrd(struct fdt_node *n, paddr_t *begin, paddr_t *end);

/** Apply an update to the FDT. */
bool fdt_patch(paddr_t fdt_addr, struct boot_params_update *p);
