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

#include "hf/api.h"

#include <assert.h>

#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

static_assert(HF_MAILBOX_SIZE == PAGE_SIZE,
	      "Currently, a page is mapped for the send and receive buffers so "
	      "the maximum request is the size of a page.");

/**
 * Switches the physical CPU back to the corresponding vcpu of the primary VM.
 *
 * This triggers the scheduling logic to run. Run in the context of secondary VM
 * to cause HF_VCPU_RUN to return and the primary VM to regain control of the
 * cpu.
 */
static struct vcpu *api_switch_to_primary(size_t primary_retval,
					  enum vcpu_state secondary_state)
{
	struct vcpu *vcpu = cpu()->current;
	struct vm *primary = vm_get(HF_PRIMARY_VM_ID);
	struct vcpu *next = &primary->vcpus[cpu_index(cpu())];

	/* Switch back to primary VM. */
	vm_set_current(primary);

	/*
	 * Set the return valuefor the primary VM's call to HF_VCPU_RUN.
	 */
	arch_regs_set_retval(&next->regs, primary_retval);

	/* Mark the vcpu as waiting. */
	sl_lock(&vcpu->lock);
	vcpu->state = secondary_state;
	sl_unlock(&vcpu->lock);

	return next;
}

/**
 * Returns to the primary vm leaving the current vcpu ready to be scheduled
 * again.
 */
struct vcpu *api_yield(void)
{
	return api_switch_to_primary(
		HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_YIELD, 0, 0),
		vcpu_state_ready);
}

/**
 * Puts the current vcpu in wait for interrupt mode, and returns to the primary
 * vm.
 */
struct vcpu *api_wait_for_interrupt(void)
{
	return api_switch_to_primary(
		HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT, 0, 0),
		vcpu_state_blocked_interrupt);
}

/**
 * Returns the number of VMs configured to run.
 */
int64_t api_vm_get_count(void)
{
	return vm_get_count();
}

/**
 * Returns the number of vcpus configured in the given VM.
 */
int64_t api_vcpu_get_count(uint32_t vm_id)
{
	struct vm *vm;

	/* Only the primary VM needs to know about vcpus for scheduling. */
	if (cpu()->current->vm->id != HF_PRIMARY_VM_ID) {
		return -1;
	}

	vm = vm_get(vm_id);
	if (vm == NULL) {
		return -1;
	}

	return vm->vcpu_count;
}

/**
 * Runs the given vcpu of the given vm.
 */
int64_t api_vcpu_run(uint32_t vm_id, uint32_t vcpu_idx, struct vcpu **next)
{
	struct vm *vm;
	struct vcpu *vcpu;
	int64_t ret;

	/* Only the primary VM can switch vcpus. */
	if (cpu()->current->vm->id != HF_PRIMARY_VM_ID) {
		goto fail;
	}

	/* Only secondary VM vcpus can be run. */
	if (vm_id == HF_PRIMARY_VM_ID) {
		goto fail;
	}

	/* The requested VM must exist. */
	vm = vm_get(vm_id);
	if (vm == NULL) {
		goto fail;
	}

	/* The requested vcpu must exist. */
	if (vcpu_idx >= vm->vcpu_count) {
		goto fail;
	}

	vcpu = &vm->vcpus[vcpu_idx];

	sl_lock(&vcpu->lock);
	if (vcpu->state != vcpu_state_ready) {
		ret = HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT, 0,
					   0);
	} else {
		vcpu->state = vcpu_state_running;
		vm_set_current(vm);
		*next = vcpu;
		ret = HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_YIELD, 0, 0);
	}
	sl_unlock(&vcpu->lock);

	return ret;

fail:
	return HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT, 0, 0);
}

/**
 * Configures the VM to send/receive data through the specified pages. The pages
 * must not be shared.
 */
int64_t api_vm_configure(ipaddr_t send, ipaddr_t recv)
{
	struct vm *vm = cpu()->current->vm;
	paddr_t pa_send_begin;
	paddr_t pa_send_end;
	paddr_t pa_recv_begin;
	paddr_t pa_recv_end;
	int64_t ret;

	/* Fail if addresses are not page-aligned. */
	if ((ipa_addr(send) & (PAGE_SIZE - 1)) ||
	    (ipa_addr(recv) & (PAGE_SIZE - 1))) {
		return -1;
	}

	sl_lock(&vm->lock);

	/* We only allow these to be setup once. */
	if (vm->mailbox.send || vm->mailbox.recv) {
		ret = -1;
		goto exit;
	}

	/*
	 * TODO: Once memory sharing is implemented, we need to make sure that
	 * these pages aren't and won't be shared.
	 */

	/*
	 * Convert the intermediate physical addresses to physical address
	 * provided the address was acessible from the VM which ensures that the
	 * caller isn't trying to use another VM's memory.
	 */
	if (!mm_vm_translate(&vm->ptable, send, &pa_send_begin) ||
	    !mm_vm_translate(&vm->ptable, recv, &pa_recv_begin)) {
		ret = -1;
		goto exit;
	}

	/* Fail if the same page is used for the send and receive pages. */
	if (pa_addr(pa_send_begin) == pa_addr(pa_recv_begin)) {
		ret = -1;
		goto exit;
	}

	pa_send_end = pa_add(pa_send_begin, PAGE_SIZE);
	pa_recv_end = pa_add(pa_recv_begin, PAGE_SIZE);

	/* Map the send page as read-only in the hypervisor address space. */
	vm->mailbox.send =
		mm_identity_map(pa_send_begin, pa_send_end, MM_MODE_R);
	if (!vm->mailbox.send) {
		ret = -1;
		goto exit;
	}

	/*
	 * Map the receive page as writable in the hypervisor address space. On
	 * failure, unmap the send page before returning.
	 */
	vm->mailbox.recv =
		mm_identity_map(pa_recv_begin, pa_recv_end, MM_MODE_W);
	if (!vm->mailbox.recv) {
		vm->mailbox.send = NULL;
		mm_unmap(pa_send_begin, pa_send_end, 0);
		ret = -1;
		goto exit;
	}

	/* TODO: Notify any waiters. */

	ret = 0;
exit:
	sl_unlock(&vm->lock);

	return ret;
}

/**
 * Copies data from the sender's send buffer to the recipient's receive buffer
 * and notifies the recipient.
 */
int64_t api_mailbox_send(uint32_t vm_id, size_t size, struct vcpu **next)
{
	struct vm *from = cpu()->current->vm;
	struct vm *to;
	const void *from_buf;
	uint16_t vcpu;
	int64_t ret;
	int64_t primary_ret;

	/* Limit the size of transfer. */
	if (size > HF_MAILBOX_SIZE) {
		return -1;
	}

	/* Disallow reflexive requests as this suggests an error in the VM. */
	if (vm_id == from->id) {
		return -1;
	}

	/* Ensure the target VM exists. */
	to = vm_get(vm_id);
	if (to == NULL) {
		return -1;
	}

	/*
	 * Check that the sender has configured its send buffer. It is safe to
	 * use from_buf after releasing the lock because the buffer cannot be
	 * modified once it's configured.
	 */
	sl_lock(&from->lock);
	from_buf = from->mailbox.send;
	sl_unlock(&from->lock);
	if (from_buf == NULL) {
		return -1;
	}

	sl_lock(&to->lock);

	if (to->mailbox.state != mailbox_state_empty ||
	    to->mailbox.recv == NULL) {
		/* Fail if the target isn't currently ready to receive data. */
		ret = -1;
		goto out;
	}

	/* Copy data. */
	memcpy(to->mailbox.recv, from_buf, size);
	to->mailbox.recv_bytes = size;
	to->mailbox.recv_from_id = from->id;
	to->mailbox.state = mailbox_state_read;

	/* Messages for the primary VM are delivered directly. */
	if (to->id == HF_PRIMARY_VM_ID) {
		primary_ret =
			HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_MESSAGE, 0, size);
		ret = 0;
		/*
		 * clang-tidy isn't able to prove that
		 * `from->id != HF_PRIMARY_VM_ID` so cover that specific case
		 * explicitly so as not to hide other possible bugs. clang-check
		 * is more clever and finds that this is dead code so we also
		 * pretend to use the new value.
		 */
		if (from->id == HF_PRIMARY_VM_ID) {
			vcpu = 0;
			(void)vcpu;
		}
		goto out;
	}

	/*
	 * Try to find a vcpu to handle the message and tell the scheduler to
	 * run it.
	 */
	if (to->mailbox.recv_waiter == NULL) {
		/*
		 * The scheduler must choose a vcpu to interrupt so it can
		 * handle the message.
		 */
		to->mailbox.state = mailbox_state_received;
		vcpu = HF_INVALID_VCPU;
	} else {
		struct vcpu *to_vcpu = to->mailbox.recv_waiter;

		/*
		 * Take target vcpu out of waiter list and mark as ready
		 * to run again.
		 */
		sl_lock(&to_vcpu->lock);
		to->mailbox.recv_waiter = to_vcpu->mailbox_next;
		to_vcpu->state = vcpu_state_ready;

		/* Return from HF_MAILBOX_RECEIVE. */
		arch_regs_set_retval(&to_vcpu->regs,
				     HF_MAILBOX_RECEIVE_RESPONSE(
					     to->mailbox.recv_from_id, size));

		sl_unlock(&to_vcpu->lock);

		vcpu = to_vcpu - to->vcpus;
	}

	/* Return to the primary VM directly or with a switch. */
	primary_ret = HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAKE_UP, to->id, vcpu);
	ret = 0;

out:
	/*
	 * Unlock before routing the return values as switching to the primary
	 * will acquire more locks and nesting the locks is avoidable.
	 */
	sl_unlock(&to->lock);

	/* Report errors to the sender. */
	if (ret != 0) {
		return ret;
	}

	/* If the sender is the primary, return the vcpu to schedule. */
	if (from->id == HF_PRIMARY_VM_ID) {
		return vcpu;
	}

	/* Switch to primary for scheduling and return success to the sender. */
	*next = api_switch_to_primary(primary_ret, vcpu_state_ready);
	return 0;
}

/**
 * Receives a message from the mailbox. If one isn't available, this function
 * can optionally block the caller until one becomes available.
 *
 * No new messages can be received until the mailbox has been cleared.
 */
int64_t api_mailbox_receive(bool block, struct vcpu **next)
{
	struct vcpu *vcpu = cpu()->current;
	struct vm *vm = vcpu->vm;
	int64_t ret = 0;

	/*
	 * The primary VM will receive messages as a status code from running
	 * vcpus and must not call this function.
	 */
	if (vm->id == HF_PRIMARY_VM_ID) {
		return -1;
	}

	sl_lock(&vm->lock);

	/* Return pending messages without blocking. */
	if (vm->mailbox.state == mailbox_state_received) {
		vm->mailbox.state = mailbox_state_read;
		ret = HF_MAILBOX_RECEIVE_RESPONSE(vm->mailbox.recv_from_id,
						  vm->mailbox.recv_bytes);
		goto out;
	}

	/* No pending message so fail if not allowed to block. */
	if (!block) {
		ret = -1;
		goto out;
	}

	sl_lock(&vcpu->lock);
	vcpu->state = vcpu_state_blocked_mailbox;

	/* Push vcpu into waiter list. */
	vcpu->mailbox_next = vm->mailbox.recv_waiter;
	vm->mailbox.recv_waiter = vcpu;
	sl_unlock(&vcpu->lock);

	/* Switch back to primary vm to block. */
	*next = api_wait_for_interrupt();

out:
	sl_unlock(&vm->lock);

	return ret;
}

/**
 * Clears the caller's mailbox so that a new message can be received. The caller
 * must have copied out all data they wish to preserve as new messages will
 * overwrite the old and will arrive asynchronously.
 */
int64_t api_mailbox_clear(void)
{
	struct vm *vm = cpu()->current->vm;
	int64_t ret;

	sl_lock(&vm->lock);
	if (vm->mailbox.state == mailbox_state_read) {
		ret = 0;
		vm->mailbox.state = mailbox_state_empty;
	} else {
		ret = -1;
	}
	sl_unlock(&vm->lock);

	if (ret == 0) {
		/* TODO: Notify waiters, if any. */
	}

	return ret;
}
