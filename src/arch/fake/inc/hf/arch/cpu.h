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

#include <stdbool.h>
#include <stdint.h>

#include "hf/addr.h"

typedef uint64_t uintreg_t;

struct arch_regs {
	uintreg_t r[5];
	uintreg_t vcpu_index;
	bool virtual_interrupt;
};

static inline void arch_irq_disable(void)
{
	/* TODO */
}

static inline void arch_irq_enable(void)
{
	/* TODO */
}

static inline void arch_regs_init(struct arch_regs *r, bool is_primary,
				  uint64_t vmid, paddr_t table, uint64_t index)
{
	/* TODO */
	(void)is_primary;
	(void)vmid;
	(void)table;
	r->vcpu_index = index;
}

static inline void arch_regs_set_pc_arg(struct arch_regs *r, ipaddr_t pc,
					uintreg_t arg)
{
	(void)pc;
	r->r[0] = arg;
}

static inline void arch_regs_set_retval(struct arch_regs *r, uintreg_t v)
{
	r->r[0] = v;
}
