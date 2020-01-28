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

#include <stdbool.h>
#include <stdint.h>

#define PAGE_BITS 12
#define PAGE_LEVEL_BITS 9
#define STACK_ALIGN 64

/** The type of a page table entry (PTE). */
typedef uint64_t pte_t;

/** Integer type large enough to hold a physical address. */
typedef uintptr_t uintpaddr_t;

/** Integer type large enough to hold a virtual address. */
typedef uintptr_t uintvaddr_t;

/** The integer corresponding to the native register size. */
typedef uint64_t uintreg_t;

/** The ID of a physical or virtual CPU. */
typedef uint32_t cpu_id_t;

/** Arch-specifc information about a VM. */
struct arch_vm {
	/* This field is only here because empty structs aren't allowed. */
	void *dummy;
};

/** Type to represent the register state of a VM. */
struct arch_regs {
	uintreg_t arg[8];
	cpu_id_t vcpu_id;
	bool virtual_interrupt;
};
