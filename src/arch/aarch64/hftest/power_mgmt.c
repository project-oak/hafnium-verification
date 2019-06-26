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

#include "hf/arch/vm/power_mgmt.h"

#include "hf/spinlock.h"
#include "hf/static_assert.h"

#include "vmapi/hf/call.h"

#include "psci.h"
#include "smc.h"

/**
 * Holds temporary state used to set up the environment on which CPUs will
 * start executing.
 *
 * vm_cpu_entry_raw requires that the first field of cpu_start_state be the
 * initial stack pointer.
 */
struct cpu_start_state {
	uintptr_t initial_sp;
	void (*entry)(uintptr_t arg);
	uintreg_t arg;
	struct spinlock lock;
};

/**
 * Releases the given cpu_start_state struct by releasing its lock, then calls
 * the entry point specified by the caller of cpu_start.
 */
void vm_cpu_entry(struct cpu_start_state *s)
{
	struct cpu_start_state local = *(volatile struct cpu_start_state *)s;

	sl_unlock(&s->lock);

	local.entry(local.arg);

	/* Turn off CPU if the entry point ever returns. */
	cpu_stop();
}

/**
 * Starts the CPU with the given ID. It will start at the provided entry point
 * with the provided argument.
 */
bool cpu_start(uintptr_t id, void *stack, size_t stack_size,
	       void (*entry)(uintptr_t arg), uintptr_t arg)
{
	void vm_cpu_entry_raw(uintptr_t arg);
	struct cpu_start_state s;

	/* Initialise the temporary state we'll hold on the stack. */
	sl_init(&s.lock);
	sl_lock(&s.lock);
	s.initial_sp = (uintptr_t)stack + stack_size;
	s.entry = entry;
	s.arg = arg;

	/* Try to start the CPU. */
	if (smc(PSCI_CPU_ON, id, (size_t)&vm_cpu_entry_raw, (size_t)&s) !=
	    PSCI_RETURN_SUCCESS) {
		return false;
	}

	/*
	 * Wait for the starting cpu to release the spin lock, which indicates
	 * that it won't touch the state we hold on the stack anymore.
	 */
	sl_lock(&s.lock);

	return true;
}

/**
 * Stops the current CPU.
 */
noreturn void cpu_stop(void)
{
	smc(PSCI_CPU_OFF, 0, 0, 0);
	for (;;) {
		/* This should never be reached. */
	}
}

static_assert(POWER_STATUS_ON == PSCI_RETURN_ON,
	      "power_status enum values must match PSCI return values.");
static_assert(POWER_STATUS_OFF == PSCI_RETURN_OFF,
	      "power_status enum values must match PSCI return values.");
static_assert(POWER_STATUS_ON_PENDING == PSCI_RETURN_ON_PENDING,
	      "power_status enum values must match PSCI return values.");

/**
 * Returns the power status of the given CPU.
 */
enum power_status cpu_status(cpu_id_t cpu_id)
{
	uint32_t lowest_affinity_level = 0;

	/*
	 * This works because the power_status enum values happen to be the same
	 * as the PSCI_RETURN_* values. The static_asserts above validate that
	 * this is the case.
	 */
	return smc(PSCI_AFFINITY_INFO, cpu_id, lowest_affinity_level, 0);
}

/**
 * Shuts down the system or exits emulation.
 */
noreturn void arch_power_off(void)
{
	smc(PSCI_SYSTEM_OFF, 0, 0, 0);
	for (;;) {
		/* This should never be reached. */
	}
}
