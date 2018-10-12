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

#if defined(__linux__) && defined(__KERNEL__)

#include <linux/types.h>

typedef phys_addr_t hf_ipaddr_t;

#define PRIu16 "hu"

#else

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef uintptr_t hf_ipaddr_t;

#endif

typedef uint16_t hf_vm_id_t;

#define HF_VM_ID_MAX UINT16_MAX
#define HF_PRI_VM_ID PRIu16

/* The ID of the primary VM which is responsile for scheduling. */
#define HF_PRIMARY_VM_ID 0
