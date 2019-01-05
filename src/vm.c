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

	vm->id = vm_count;
	vm->vcpu_count = vcpu_count;
	vm->mailbox.state = mailbox_state_empty;

	if (!mm_vm_init(&vm->ptable, ppool)) {
		return false;
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

/* TODO: Shall we use index or id here? */
void vm_start_vcpu(struct vm *vm, size_t index, ipaddr_t entry, uintreg_t arg)
{
	struct vcpu *vcpu = &vm->vcpus[index];
	if (index < vm->vcpu_count) {
		arch_regs_set_pc_arg(&vcpu->regs, entry, arg);
		vcpu_on(vcpu);
	}
}
