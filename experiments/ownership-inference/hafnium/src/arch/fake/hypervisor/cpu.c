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

#include "hf/arch/cpu.h"

#include "hf/cpu.h"
#include "hf/spci.h"

void arch_irq_disable(void)
{
	/* TODO */
}

void arch_irq_enable(void)
{
	/* TODO */
}

void arch_regs_reset(struct vcpu *vcpu)
{
	/* TODO */
	(void)vcpu;
}

void arch_regs_set_pc_arg(struct arch_regs *r, ipaddr_t pc, uintreg_t arg)
{
	(void)pc;
	r->arg[0] = arg;
}

void arch_regs_set_retval(struct arch_regs *r, struct spci_value v)
{
	r->arg[0] = v.func;
	r->arg[1] = v.arg1;
	r->arg[2] = v.arg2;
	r->arg[3] = v.arg3;
	r->arg[4] = v.arg4;
	r->arg[5] = v.arg5;
	r->arg[6] = v.arg6;
	r->arg[7] = v.arg7;
}
