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

#include "hf/cpu.h"

#include <stdbool.h>
#include <stddef.h>

#include "hf/arch/cpu.h"

#include "hf/addr.h"
#include "hf/dlog.h"

#include "msr.h"

#define HCR_EL2_VI (1u << 7)

void arch_regs_set_virtual_interrupt(struct arch_regs *r, bool enable)
{
	if (enable) {
		r->lazy.hcr_el2 |= HCR_EL2_VI;
	} else {
		r->lazy.hcr_el2 &= ~HCR_EL2_VI;
	}
	if (&current()->regs == r) {
		write_msr(hcr_el2, r->lazy.hcr_el2);
	}
}
