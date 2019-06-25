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

#include "hf/vm.h"

#include "hf/api.h"
#include "hf/cpu.h"
#include "hf/spci.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

static struct vm vms[MAX_VMS];
static spci_vm_count_t vm_count;

bool vm_init(uint32_t vcpu_count, struct mpool *ppool, struct vm **new_vm)
{
	uint32_t i;
	struct vm *vm;

	if (vm_count >= MAX_VMS) {
		return false;
	}

	vm = &vms[vm_count];

	memset_s(vm, sizeof(*vm), 0, sizeof(*vm));

	list_init(&vm->mailbox.waiter_list);
	list_init(&vm->mailbox.ready_list);
	sl_init(&vm->lock);

	vm->id = vm_count;
	vm->vcpu_count = vcpu_count;
	vm->mailbox.state = MAILBOX_STATE_EMPTY;
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
		vcpu_init(vm_get_vcpu(vm, i), vm);
	}

	++vm_count;
	*new_vm = vm;

	return true;
}

spci_vm_count_t vm_get_count(void)
{
	return vm_count;
}

struct vm *vm_find(spci_vm_id_t id)
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
struct vm_locked vm_lock(struct vm *vm)
{
	struct vm_locked locked = {
		.vm = vm,
	};

	sl_lock(&vm->lock);

	return locked;
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
 * Get the vCPU with the given index from the given VM.
 * This assumes the index is valid, i.e. less than vm->vcpu_count.
 */
struct vcpu *vm_get_vcpu(struct vm *vm, spci_vcpu_index_t vcpu_index)
{
	assert(vcpu_index < vm->vcpu_count);
	return &vm->vcpus[vcpu_index];
}
