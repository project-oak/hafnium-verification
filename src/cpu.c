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

#include <stdalign.h>

#include "hf/arch/cpu.h"

#include "hf/api.h"
#include "hf/dlog.h"
#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

#define STACK_SIZE PAGE_SIZE

/* The stack to be used by the CPUs. */
alignas(2 * sizeof(uintreg_t)) static char callstacks[MAX_CPUS][STACK_SIZE];

/* State of all supported CPUs. The stack of the first one is initialized. */
struct cpu cpus[MAX_CPUS] = {
	{
		.is_on = 1,
		.stack_bottom = &callstacks[0][STACK_SIZE],
	},
};

void cpu_module_init(void)
{
	size_t i;

	/* Initialize all CPUs. */
	for (i = 0; i < MAX_CPUS; i++) {
		struct cpu *c = &cpus[i];

		cpu_init(c);
		c->id = i; /* TODO: Initialize ID based on fdt. */
		c->stack_bottom = &callstacks[i][STACK_SIZE];
	}
}

size_t cpu_index(struct cpu *c)
{
	return c - cpus;
}

void cpu_init(struct cpu *c)
{
	/* TODO: Assumes that c is zeroed out already. */
	sl_init(&c->lock);
	c->irq_disable_count = 1;
}

void cpu_irq_enable(struct cpu *c)
{
	c->irq_disable_count--;
	if (!c->irq_disable_count) {
		arch_irq_enable();
	}
}

void cpu_irq_disable(struct cpu *c)
{
	if (!c->irq_disable_count) {
		arch_irq_disable();
	}
	c->irq_disable_count++;
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
		struct vm *vm = vm_get(HF_PRIMARY_VM_ID);
		struct vcpu *vcpu = &vm->vcpus[cpu_index(c)];

		vcpu_on(vcpu, entry, arg);
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
 * Searches for a CPU based on its id.
 */
struct cpu *cpu_find(size_t id)
{
	size_t i;

	for (i = 0; i < MAX_CPUS; i++) {
		if (cpus[i].id == id) {
			return &cpus[i];
		}
	}

	return NULL;
}

void vcpu_init(struct vcpu *vcpu, struct vm *vm)
{
	memset(vcpu, 0, sizeof(*vcpu));
	sl_init(&vcpu->lock);
	vcpu->regs_available = true;
	vcpu->vm = vm;
	vcpu->state = vcpu_state_off;
}

void vcpu_on(struct vcpu *vcpu, ipaddr_t entry, uintreg_t arg)
{
	arch_regs_set_pc_arg(&vcpu->regs, entry, arg);

	sl_lock(&vcpu->lock);
	vcpu->state = vcpu_state_ready;
	sl_unlock(&vcpu->lock);
}

void vcpu_off(struct vcpu *vcpu)
{
	sl_lock(&vcpu->lock);
	vcpu->state = vcpu_state_off;
	sl_unlock(&vcpu->lock);
}

size_t vcpu_index(const struct vcpu *vcpu)
{
	return vcpu - vcpu->vm->vcpus;
}

/**
 * Handles a page fault. It does so by determining if it's a legitimate or
 * spurious fault, and recovering from the latter.
 *
 * Returns true if the caller should resume the current vcpu, or false if its VM
 * should be aborted.
 */
bool vcpu_handle_page_fault(const struct vcpu *current,
			    struct vcpu_fault_info *f)
{
	struct vm *vm = current->vm;
	ipaddr_t second_addr;
	bool second;
	int mode;
	int mask = f->mode | MM_MODE_INVALID;
	bool ret = false;

	/* We can't recover if we don't know the size. */
	if (f->size == 0) {
		goto exit;
	}

	sl_lock(&vm->lock);

	/*
	 * Check if this is a legitimate fault, i.e., if the page table doesn't
	 * allow the access attemped by the VM.
	 */
	if (!mm_vm_get_mode(&vm->ptable, f->ipaddr, ipa_add(f->ipaddr, 1),
			    &mode) ||
	    (mode & mask) != f->mode) {
		goto exit_unlock;
	}

	/*
	 * Do the same mode check on the second page, if the fault straddles two
	 * pages.
	 */
	second_addr = ipa_add(f->ipaddr, f->size - 1);
	second = (ipa_addr(f->ipaddr) >> PAGE_BITS) !=
		 (ipa_addr(second_addr) >> PAGE_BITS);
	if (second) {
		if (!mm_vm_get_mode(&vm->ptable, second_addr,
				    ipa_add(second_addr, 1), &mode) ||
		    (mode & mask) != f->mode) {
			goto exit_unlock;
		}
	}

	/*
	 * This is a spurious fault, likely because another CPU is updating the
	 * page table. It is responsible for issuing global tlb invalidations
	 * while holding the VM lock, so we don't need to do anything else to
	 * recover from it. (Acquiring/releasing the lock ensured that the
	 * invalidations have completed.)
	 */

	ret = true;

exit_unlock:
	sl_unlock(&vm->lock);
exit:
	if (!ret) {
		dlog("Stage-2 page fault: pc=0x%x, vmid=%u, vcpu=%u, "
		     "vaddr=0x%x, ipaddr=0x%x, mode=0x%x, size=%u\n",
		     f->pc, vm->id, vcpu_index(current), f->vaddr, f->ipaddr,
		     f->mode, f->size);
	}
	return ret;
}
