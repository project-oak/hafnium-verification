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

#include "hf/arch/vm/power_mgmt.h"

#include "hf/arch/mm.h"

#include "hf/spinlock.h"

#include "hftest.h"

struct cpu_start_state {
	void (*entry)(uintptr_t arg);
	uintreg_t arg;
	struct spinlock lock;
};

static noreturn void cpu_entry(uintptr_t arg)
{
	struct cpu_start_state *s = (struct cpu_start_state *)arg;
	struct cpu_start_state s_copy;

	/*
	 * Initialize memory and enable caching. Must be the first thing we do.
	 */
	hftest_mm_vcpu_init();

	/* Make a copy of the cpu_start_state struct. */
	s_copy = *s;

	/* Inform cpu_start() that the state struct memory can now be freed. */
	sl_unlock(&s->lock);

	/* Call the given entry function with the given argument. */
	s_copy.entry(s_copy.arg);

	/* If the entry function returns, turn off the CPU. */
	arch_cpu_stop();
}

bool hftest_cpu_start(uintptr_t id, void *stack, size_t stack_size,
		      void (*entry)(uintptr_t arg), uintptr_t arg)
{
	struct cpu_start_state s;
	struct arch_cpu_start_state s_arch;

	/*
	 * Config for arch_cpu_start() which will start a new CPU and
	 * immediately jump to cpu_entry(). This function must guarantee that
	 * the state struct is not be freed until cpu_entry() is called.
	 */
	s_arch.initial_sp = (uintptr_t)stack + stack_size;
	s_arch.entry = cpu_entry;
	s_arch.arg = (uintptr_t)&s;

	/*
	 * Flush the `cpu_start_state` struct because the new CPU will be
	 * started without caching enabled and will need the data early on.
	 * Write back is all that is really needed so flushing will definitely
	 * get the job done.
	 */
	arch_mm_flush_dcache(&s_arch, sizeof(s_arch));

	if ((s_arch.initial_sp % STACK_ALIGN) != 0) {
		HFTEST_FAIL(true,
			    "Stack pointer of new vCPU not properly aligned.");
	}

	/*
	 * Config for cpu_entry(). Its job is to initialize memory and call the
	 * provided entry point with the provided argument.
	 */
	s.entry = entry;
	s.arg = arg;
	sl_init(&s.lock);

	/*
	 * Lock the cpu_start_state struct which will be unlocked once
	 * cpu_entry() does not need its content anymore. This simultaneously
	 * protects the arch_cpu_start_state struct which must not be freed
	 * before cpu_entry() is called.
	 */
	sl_lock(&s.lock);

	/* Try to start the given CPU. */
	if (!arch_cpu_start(id, &s_arch)) {
		return false;
	}

	/*
	 * Wait until cpu_entry() unlocks the cpu_start_state lock before
	 * freeing stack memory.
	 */
	sl_lock(&s.lock);
	return true;
}
