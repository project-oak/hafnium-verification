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

#include <stdint.h>

#define PAGE_BITS 12
#define PAGE_LEVEL_BITS 9

/** The type of a page table entry (PTE). */
typedef uint64_t pte_t;

/** Integer type large enough to hold a physical address. */
typedef uintptr_t uintpaddr_t;

/** Integer type large enough to hold a virtual address. */
typedef uintptr_t uintvaddr_t;

/** The integer large corresponding to the native register size. */
typedef uint64_t uintreg_t;

/** Type to represent the register state of a VM.  */
struct arch_regs {
	/* General purpose registers. */
	uintreg_t r[31];
	uintreg_t pc;
	uintreg_t spsr;

	struct {
		uintreg_t vmpidr_el2;
		uintreg_t csselr_el1;
		uintreg_t sctlr_el1;
		uintreg_t actlr_el1;
		uintreg_t cpacr_el1;
		uintreg_t ttbr0_el1;
		uintreg_t ttbr1_el1;
		uintreg_t tcr_el1;
		uintreg_t esr_el1;
		uintreg_t afsr0_el1;
		uintreg_t afsr1_el1;
		uintreg_t far_el1;
		uintreg_t mair_el1;
		uintreg_t vbar_el1;
		uintreg_t contextidr_el1;
		uintreg_t tpidr_el0;
		uintreg_t tpidrro_el0;
		uintreg_t tpidr_el1;
		uintreg_t amair_el1;
		uintreg_t cntkctl_el1;
		uintreg_t sp_el0;
		uintreg_t sp_el1;
		uintreg_t elr_el1;
		uintreg_t spsr_el1;
		uintreg_t par_el1;
		uintreg_t hcr_el2;
		uintreg_t cptr_el2;
		uintreg_t cnthctl_el2;
		uintreg_t vttbr_el2;
		uintreg_t cntv_cval_el0;
		uintreg_t cntv_ctl_el0;
	} lazy;
};
