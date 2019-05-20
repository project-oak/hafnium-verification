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

#pragma once

#include "hf/mpool.h"
#include "hf/vm.h"

/** Initialises the console hardware. */
void plat_console_init(void);

/** Initialises any memory mappings that the console driver needs. */
void plat_console_mm_init(struct mpool *ppool);

/** Initialises any per-VM memory mappings that the console driver needs. */
void plat_console_vm_mm_init(struct vm *vm, struct mpool *ppool);

/** Puts a single character on the console. */
void plat_console_putchar(char c);
