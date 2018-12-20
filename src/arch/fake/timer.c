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

#include "hf/arch/timer.h"

#include <stdbool.h>
#include <stdint.h>

#include "hf/arch/types.h"

bool arch_timer_pending(struct arch_regs *regs)
{
	/* TODO */
	(void)regs;
	return false;
}

void arch_timer_mask(struct arch_regs *regs)
{
	/* TODO */
	(void)regs;
}

bool arch_timer_enabled(struct arch_regs *regs)
{
	/* TODO */
	(void)regs;
	return false;
}

uint64_t arch_timer_remaining_ns(struct arch_regs *regs)
{
	/* TODO */
	(void)regs;
	return 0;
}

bool arch_timer_enabled_current(void)
{
	/* TODO */
	return false;
}

uint64_t arch_timer_remaining_ns_current(void)
{
	/* TODO */
	return 0;
}
