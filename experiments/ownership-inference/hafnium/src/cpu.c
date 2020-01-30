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

#include "hf/cpu.h"

#include <stdalign.h>

#include "hf/api.h"
#include "hf/check.h"
#include "hf/dlog.h"

#include "vmapi/hf/call.h"

#define STACK_SIZE PAGE_SIZE

/**
 * The stacks to be used by the CPUs.
 *
 * Align to page boundaries to ensure that cache lines are not shared between a
 * CPU's stack and data that can be accessed from other CPUs. If this did
 * happen, there may be coherency problems when the stack is being used before
 * caching is enabled.
 */
alignas(PAGE_SIZE) static char callstacks[MAX_CPUS][STACK_SIZE];

/* NOLINTNEXTLINE(misc-redundant-expression) */
static_assert((STACK_SIZE % PAGE_SIZE) == 0, "Keep each stack page aligned.");
static_assert((PAGE_SIZE % STACK_ALIGN) == 0,
	      "Page alignment is too weak for the stack.");

/**
 * Internal buffer used to store SPCI messages from a VM Tx. Its usage prevents
 * TOCTOU issues while Hafnium performs actions on information that would
 * otherwise be re-writable by the VM.
 *
 * Each buffer is owned by a single CPU. The buffer can only be used for
 * spci_msg_send. The information stored in the buffer is only valid during the
 * spci_msg_send request is performed.
 */
alignas(PAGE_SIZE) static uint8_t cpu_message_buffer[MAX_CPUS][PAGE_SIZE];

uint8_t *cpu_get_buffer(struct cpu *c)
{
	size_t cpu_indx = cpu_index(c);

	CHECK(cpu_indx < MAX_CPUS);

	return cpu_message_buffer[cpu_indx];
}

uint32_t cpu_get_buffer_size(struct cpu *c)
{
	size_t cpu_indx = cpu_index(c);

	CHECK(cpu_indx < MAX_CPUS);

	return sizeof(cpu_message_buffer[cpu_indx]);
}

/* State of all supported CPUs. The stack of the first one is initialized. */
struct cpu cpus[MAX_CPUS] = {
	{
		.is_on = 1,
		.stack_bottom = &callstacks[0][STACK_SIZE],
	},
};

static uint32_t cpu_count = 1;

void cpu_module_init(const cpu_id_t *cpu_ids, size_t count)
{
	uint32_t i;
	uint32_t j;
	cpu_id_t boot_cpu_id = cpus[0].id;
	bool found_boot_cpu = false;

	cpu_count = count;

	/*
	 * Initialize CPUs with the IDs from the configuration passed in. The
	 * CPUs after the boot CPU are initialized in reverse order. The boot
	 * CPU is initialized when it is found or in place of the last CPU if it
	 * is not found.
	 */
	j = cpu_count;
	for (i = 0; i < cpu_count; ++i) {
		struct cpu *c;
		cpu_id_t id = cpu_ids[i];

		if (found_boot_cpu || id != boot_cpu_id) {
			--j;
			c = &cpus[j];
			c->stack_bottom = &callstacks[j][STACK_SIZE];
		} else {
			found_boot_cpu = true;
			c = &cpus[0];
			CHECK(c->stack_bottom == &callstacks[0][STACK_SIZE]);
		}

		sl_init(&c->lock);
		c->id = id;
	}

	if (!found_boot_cpu) {
		/* Boot CPU was initialized but with wrong ID. */
		dlog("Boot CPU's ID not found in config.\n");
		cpus[0].id = boot_cpu_id;
	}
}

size_t cpu_index(struct cpu *c)
{
	return c - cpus;
}

/**
 * Turns CPU on and returns the previous state.
 */
bool cpu_on(struct cpu *c, ipaddr_t entry, uintreg_t arg)
{
	bool prev;

	sl_lock(&c->lock);
	prev = c->is_on;
	c->is_on = true;
	sl_unlock(&c->lock);

	if (!prev) {
		struct vm *vm = vm_find(HF_PRIMARY_VM_ID);
		struct vcpu *vcpu = vm_get_vcpu(vm, cpu_index(c));
		struct vcpu_locked vcpu_locked;

		vcpu_locked = vcpu_lock(vcpu);
		vcpu_on(vcpu_locked, entry, arg);
		vcpu_unlock(&vcpu_locked);
	}

	return prev;
}

/**
 * Prepares the CPU for turning itself off.
 */
void cpu_off(struct cpu *c)
{
	sl_lock(&c->lock);
	c->is_on = false;
	sl_unlock(&c->lock);
}

/**
 * Searches for a CPU based on its ID.
 */
struct cpu *cpu_find(cpu_id_t id)
{
	size_t i;

	for (i = 0; i < cpu_count; i++) {
		if (cpus[i].id == id) {
			return &cpus[i];
		}
	}

	return NULL;
}
