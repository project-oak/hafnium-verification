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
#include "hf/check.h"
#include "hf/cpu.h"
#include "hf/layout.h"
#include "hf/plat/iommu.h"
#include "hf/spci.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

static struct vm vms[MAX_VMS];
static struct vm tee_vm;
static spci_vm_count_t vm_count;

struct vm *vm_init(spci_vm_id_t id, spci_vcpu_count_t vcpu_count,
		   struct mpool *ppool)
{
	uint32_t i;
	struct vm *vm;

	if (id == HF_TEE_VM_ID) {
		vm = &tee_vm;
	} else {
		uint16_t vm_index = id - HF_VM_ID_OFFSET;

		CHECK(id >= HF_VM_ID_OFFSET);
		CHECK(vm_index < ARRAY_SIZE(vms));
		vm = &vms[vm_index];
	}

	memset_s(vm, sizeof(*vm), 0, sizeof(*vm));

	list_init(&vm->mailbox.waiter_list);
	list_init(&vm->mailbox.ready_list);
	sl_init(&vm->lock);

	vm->id = id;
	vm->vcpu_count = vcpu_count;
	vm->mailbox.state = MAILBOX_STATE_EMPTY;
	atomic_init(&vm->aborting, false);

	if (!mm_vm_init(&vm->ptable, ppool)) {
		return NULL;
	}

	/* Initialise waiter entries. */
	for (i = 0; i < MAX_VMS; i++) {
		vm->wait_entries[i].waiting_vm = vm;
		list_init(&vm->wait_entries[i].wait_links);
		list_init(&vm->wait_entries[i].ready_links);
	}

	/* Do basic initialization of vCPUs. */
	for (i = 0; i < vcpu_count; i++) {
		vcpu_init(vm_get_vcpu(vm, i), vm);
	}

	return vm;
}

bool vm_init_next(spci_vcpu_count_t vcpu_count, struct mpool *ppool,
		  struct vm **new_vm)
{
	if (vm_count >= MAX_VMS) {
		return false;
	}

	/* Generate IDs based on an offset, as low IDs e.g., 0, are reserved */
	*new_vm = vm_init(vm_count + HF_VM_ID_OFFSET, vcpu_count, ppool);
	if (*new_vm == NULL) {
		return false;
	}
	++vm_count;

	return true;
}

spci_vm_count_t vm_get_count(void)
{
	return vm_count;
}

struct vm *vm_find(spci_vm_id_t id)
{
	uint16_t index;

	/* Check that this is not a reserved ID. */
	if (id < HF_VM_ID_OFFSET) {
		return NULL;
	}

	if (id == HF_TEE_VM_ID) {
		if (tee_vm.id == HF_TEE_VM_ID) {
			return &tee_vm;
		}
		return NULL;
	}

	index = id - HF_VM_ID_OFFSET;

	/* Ensure the VM is initialized. */
	if (index >= vm_count) {
		return NULL;
	}

	return &vms[index];
}

/**
 * Locks the given VM and updates `locked` to hold the newly locked VM.
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
 * Locks two VMs ensuring that the locking order is according to the locks'
 * addresses.
 */
struct two_vm_locked vm_lock_both(struct vm *vm1, struct vm *vm2)
{
	struct two_vm_locked dual_lock;

	sl_lock_both(&vm1->lock, &vm2->lock);
	dual_lock.vm1.vm = vm1;
	dual_lock.vm2.vm = vm2;

	return dual_lock;
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
	CHECK(vcpu_index < vm->vcpu_count);
	return &vm->vcpus[vcpu_index];
}

/**
 * Gets `vm`'s wait entry for waiting on the `for_vm`.
 */
struct wait_entry *vm_get_wait_entry(struct vm *vm, spci_vm_id_t for_vm)
{
	uint16_t index;

	CHECK(for_vm >= HF_VM_ID_OFFSET);
	index = for_vm - HF_VM_ID_OFFSET;
	CHECK(index < MAX_VMS);

	return &vm->wait_entries[index];
}

/**
 * Gets the ID of the VM which the given VM's wait entry is for.
 */
spci_vm_id_t vm_id_for_wait_entry(struct vm *vm, struct wait_entry *entry)
{
	uint16_t index = entry - vm->wait_entries;

	return index + HF_VM_ID_OFFSET;
}

/**
 * Map a range of addresses to the VM in both the MMU and the IOMMU.
 *
 * mm_vm_defrag should always be called after a series of page table updates,
 * whether they succeed or fail. This is because on failure extra page table
 * entries may have been allocated and then not used, while on success it may be
 * possible to compact the page table by merging several entries into a block.
 *
 * Returns true on success, or false if the update failed and no changes were
 * made.
 *
 */
bool vm_identity_map(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
		     uint32_t mode, struct mpool *ppool, ipaddr_t *ipa)
{
	if (!vm_identity_prepare(vm_locked, begin, end, mode, ppool)) {
		return false;
	}

	vm_identity_commit(vm_locked, begin, end, mode, ppool, ipa);

	return true;
}

/**
 * Prepares the given VM for the given address mapping such that it will be able
 * to commit the change without failure.
 *
 * In particular, multiple calls to this function will result in the
 * corresponding calls to commit the changes to succeed.
 *
 * Returns true on success, or false if the update failed and no changes were
 * made.
 */
bool vm_identity_prepare(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
			 uint32_t mode, struct mpool *ppool)
{
	return mm_vm_identity_prepare(&vm_locked.vm->ptable, begin, end, mode,
				      ppool);
}

/**
 * Commits the given address mapping to the VM assuming the operation cannot
 * fail. `vm_identity_prepare` must used correctly before this to ensure
 * this condition.
 */
void vm_identity_commit(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
			uint32_t mode, struct mpool *ppool, ipaddr_t *ipa)
{
	mm_vm_identity_commit(&vm_locked.vm->ptable, begin, end, mode, ppool,
			      ipa);
	plat_iommu_identity_map(vm_locked, begin, end, mode);
}

/**
 * Unmap a range of addresses from the VM.
 *
 * Returns true on success, or false if the update failed and no changes were
 * made.
 */
bool vm_unmap(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
	      struct mpool *ppool)
{
	uint32_t mode = MM_MODE_UNMAPPED_MASK;

	return vm_identity_map(vm_locked, begin, end, mode, ppool, NULL);
}

/**
 * Unmaps the hypervisor pages from the given page table.
 */
bool vm_unmap_hypervisor(struct vm_locked vm_locked, struct mpool *ppool)
{
	/* TODO: If we add pages dynamically, they must be included here too. */
	return vm_unmap(vm_locked, layout_text_begin(), layout_text_end(),
			ppool) &&
	       vm_unmap(vm_locked, layout_rodata_begin(), layout_rodata_end(),
			ppool) &&
	       vm_unmap(vm_locked, layout_data_begin(), layout_data_end(),
			ppool);
}
