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

#include "hf/vm.h"

#include "hf/api.h"
#include "hf/cpu.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

static struct vm vms[MAX_VMS];
static uint32_t vm_count;

bool vm_init(uint32_t vcpu_count, struct mpool *ppool, struct vm **new_vm)
{
	uint32_t i;
	struct vm *vm;

	if (vm_count >= MAX_VMS) {
		return false;
	}

	vm = &vms[vm_count];

	memset(vm, 0, sizeof(*vm));

	list_init(&vm->mailbox.waiter_list);
	list_init(&vm->mailbox.ready_list);
	sl_init(&vm->lock);

	vm->id = vm_count;
	vm->vcpu_count = vcpu_count;
	vm->mailbox.state = mailbox_state_empty;
	atomic_init(&vm->aborting, false);

	if (!mm_vm_init(&vm->ptable, ppool)) {
		return false;
	}

	/* Initialise waiter entries. */
	for (i = 0; i < MAX_VMS; i++) {
		vm->wait_entries[i].waiting_vm = vm;
		list_init(&vm->wait_entries[i].wait_links);
		list_init(&vm->wait_entries[i].ready_links);
	}

	/* Do basic initialization of vcpus. */
	for (i = 0; i < vcpu_count; i++) {
		vcpu_init(&vm->vcpus[i], vm);
	}

	++vm_count;
	*new_vm = vm;

	return true;
}

uint32_t vm_get_count(void)
{
	return vm_count;
}

struct vm *vm_get(uint32_t id)
{
	/* Ensure the VM is initialized. */
	if (id >= vm_count) {
		return NULL;
	}

	return &vms[id];
}

/**
 * Locks the given VM and updates `locked` to hold the newly locked vm.
 */
void vm_lock(struct vm *vm, struct vm_locked *locked)
{
	sl_lock(&vm->lock);
	locked->vm = vm;
}

/**
 * Unlocks a VM previously locked with vm_lock, and updates `locked` to reflect
 * the fact that the VM is no longer locked.
 */
void vm_unlock(struct vm_locked *locked)
{
	sl_unlock(&locked->vm->lock);
	locked->vm = NULL;
}

/**
 * Starts a vCPU of a secondary VM.
 *
 * TODO: Shall we use index or id here?
 */
void vm_secondary_start_vcpu(struct vm *vm, size_t index, ipaddr_t entry,
			     uintreg_t arg)
{
	struct vcpu *vcpu = &vm->vcpus[index];

	if (index >= vm->vcpu_count) {
		return;
	}

	/*
	 * Set vCPU registers to a clean state ready for boot. As this is a
	 * secondary which can migrate between pCPUs, the ID of the vCPU is
	 * defined as the index and does not match the ID of the pCPU it is
	 * running on.
	 */
	arch_regs_reset(&vcpu->regs, vm->id == HF_PRIMARY_VM_ID, vm->id, index,
			vm->ptable.root);
	vcpu_on(vcpu, entry, arg);
}
