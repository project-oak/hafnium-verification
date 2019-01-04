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

#include "hf/arch/cpu.h"

#include "hf/dlog.h"
#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

/*
 * To eliminate the risk of deadlocks, we define a partial order for the
 * acquisition of locks held concurrently by the same physical CPU. Our current
 * ordering requirements are as follows:
 *
 * vm::lock -> vcpu::lock
 */

static_assert(HF_MAILBOX_SIZE == PAGE_SIZE,
	      "Currently, a page is mapped for the send and receive buffers so "
	      "the maximum request is the size of a page.");

static struct mpool api_page_pool;

/**
 * Initialises the API page pool by taking ownership of the contents of the
 * given page pool.
 */
void api_init(struct mpool *ppool)
{
	mpool_init_from(&api_page_pool, ppool);
}

/**
 * Switches the physical CPU back to the corresponding vcpu of the primary VM.
 *
 * This triggers the scheduling logic to run. Run in the context of secondary VM
 * to cause HF_VCPU_RUN to return and the primary VM to regain control of the
 * cpu.
 */
static struct vcpu *api_switch_to_primary(struct vcpu *current,
					  struct hf_vcpu_run_return primary_ret,
					  enum vcpu_state secondary_state)
{
	struct vm *primary = vm_get(HF_PRIMARY_VM_ID);
	struct vcpu *next = &primary->vcpus[cpu_index(current->cpu)];

	/* Set the return value for the primary VM's call to HF_VCPU_RUN. */
	arch_regs_set_retval(&next->regs,
			     hf_vcpu_run_return_encode(primary_ret));

	/* Mark the current vcpu as waiting. */
	sl_lock(&current->lock);
	current->state = secondary_state;
	sl_unlock(&current->lock);

	return next;
}

/**
 * Returns to the primary vm leaving the current vcpu ready to be scheduled
 * again.
 */
struct vcpu *api_yield(struct vcpu *current)
{
	struct hf_vcpu_run_return ret = {
		.code = HF_VCPU_RUN_YIELD,
	};

	return api_switch_to_primary(current, ret, vcpu_state_ready);
}

/**
 * Puts the current vcpu in wait for interrupt mode, and returns to the primary
 * vm.
 */
struct vcpu *api_wait_for_interrupt(struct vcpu *current)
{
	struct hf_vcpu_run_return ret = {
		.code = HF_VCPU_RUN_WAIT_FOR_INTERRUPT,
	};

	return api_switch_to_primary(current, ret,
				     vcpu_state_blocked_interrupt);
}

/**
 * Returns the ID of the VM.
 */
int64_t api_vm_get_id(const struct vcpu *current)
{
	return current->vm->id;
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
int64_t api_vcpu_get_count(uint32_t vm_id, const struct vcpu *current)
{
	struct vm *vm;

	/* Only the primary VM needs to know about vcpus for scheduling. */
	if (current->vm->id != HF_PRIMARY_VM_ID) {
		return -1;
	}

	vm = vm_get(vm_id);
	if (vm == NULL) {
		return -1;
	}

	return vm->vcpu_count;
}

/**
 * This function is called by the architecture-specific context switching
 * function to indicate that register state for the given vcpu has been saved
 * and can therefore be used by other pcpus.
 */
void api_regs_state_saved(struct vcpu *vcpu)
{
	sl_lock(&vcpu->lock);
	vcpu->regs_available = true;
	sl_unlock(&vcpu->lock);
}

/**
 * Prepares the vcpu to run by updating its state and fetching whether a return
 * value needs to be forced onto the vCPU.
 */
static bool api_vcpu_prepare_run(const struct vcpu *current, struct vcpu *vcpu,
				 struct retval_state *vcpu_retval)
{
	bool ret;

	sl_lock(&vcpu->lock);
	if (vcpu->state != vcpu_state_ready) {
		ret = false;
		goto out;
	}

	vcpu->cpu = current->cpu;
	vcpu->state = vcpu_state_running;

	/* Fetch return value to inject into vCPU if there is one. */
	*vcpu_retval = vcpu->retval;
	if (vcpu_retval->force) {
		vcpu->retval.force = false;
	}

	/*
	 * Wait until the registers become available. Care must be taken when
	 * looping on this: it shouldn't be done while holding other locks to
	 * avoid deadlocks.
	 */
	while (!vcpu->regs_available) {
		sl_unlock(&vcpu->lock);
		sl_lock(&vcpu->lock);
	}

	/*
	 * Mark the registers as unavailable now that we're about to reflect
	 * them onto the real registers. This will also prevent another physical
	 * CPU from trying to read these registers.
	 */
	vcpu->regs_available = false;

	ret = true;

out:
	sl_unlock(&vcpu->lock);
	return ret;
}

/**
 * Runs the given vcpu of the given vm.
 */
struct hf_vcpu_run_return api_vcpu_run(uint32_t vm_id, uint32_t vcpu_idx,
				       const struct vcpu *current,
				       struct vcpu **next)
{
	struct vm *vm;
	struct vcpu *vcpu;
	struct retval_state vcpu_retval;
	struct hf_vcpu_run_return ret = {
		.code = HF_VCPU_RUN_WAIT_FOR_INTERRUPT,
	};

	/* Only the primary VM can switch vcpus. */
	if (current->vm->id != HF_PRIMARY_VM_ID) {
		goto out;
	}

	/* Only secondary VM vcpus can be run. */
	if (vm_id == HF_PRIMARY_VM_ID) {
		goto out;
	}

	/* The requested VM must exist. */
	vm = vm_get(vm_id);
	if (vm == NULL) {
		goto out;
	}

	/* The requested vcpu must exist. */
	if (vcpu_idx >= vm->vcpu_count) {
		goto out;
	}

	/* Update state if allowed. */
	vcpu = &vm->vcpus[vcpu_idx];
	if (!api_vcpu_prepare_run(current, vcpu, &vcpu_retval)) {
		ret.code = HF_VCPU_RUN_WAIT_FOR_INTERRUPT;
		goto out;
	}

	*next = vcpu;
	ret.code = HF_VCPU_RUN_YIELD;

	/* Update return value if one was injected. */
	if (vcpu_retval.force) {
		arch_regs_set_retval(&vcpu->regs, vcpu_retval.value);
	}

out:
	return ret;
}

/**
 * Configures the VM to send/receive data through the specified pages. The pages
 * must not be shared.
 */
int64_t api_vm_configure(ipaddr_t send, ipaddr_t recv,
			 const struct vcpu *current)
{
	struct vm *vm = current->vm;
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

	/* Ensure the pages are accessible from the VM. */
	if (!mm_vm_is_mapped(&vm->ptable, send, 0) ||
	    !mm_vm_is_mapped(&vm->ptable, recv, 0)) {
		ret = -1;
		goto exit;
	}

	/* Convert to physical addresses. */
	pa_send_begin = pa_from_ipa(send);
	pa_send_end = pa_add(pa_send_begin, PAGE_SIZE);

	pa_recv_begin = pa_from_ipa(recv);
	pa_recv_end = pa_add(pa_recv_begin, PAGE_SIZE);

	/* Fail if the same page is used for the send and receive pages. */
	if (pa_addr(pa_send_begin) == pa_addr(pa_recv_begin)) {
		ret = -1;
		goto exit;
	}

	/* Map the send page as read-only in the hypervisor address space. */
	vm->mailbox.send = mm_identity_map(pa_send_begin, pa_send_end,
					   MM_MODE_R, &api_page_pool);
	if (!vm->mailbox.send) {
		ret = -1;
		goto exit;
	}

	/*
	 * Map the receive page as writable in the hypervisor address space. On
	 * failure, unmap the send page before returning.
	 */
	vm->mailbox.recv = mm_identity_map(pa_recv_begin, pa_recv_end,
					   MM_MODE_W, &api_page_pool);
	if (!vm->mailbox.recv) {
		vm->mailbox.send = NULL;
		mm_unmap(pa_send_begin, pa_send_end, 0, &api_page_pool);
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
int64_t api_mailbox_send(uint32_t vm_id, size_t size, struct vcpu *current,
			 struct vcpu **next)
{
	struct vm *from = current->vm;
	struct vm *to;
	const void *from_buf;
	uint16_t vcpu;
	int64_t ret;

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
		struct hf_vcpu_run_return primary_ret = {
			.code = HF_VCPU_RUN_MESSAGE,
			.message.size = size,
		};

		*next = api_switch_to_primary(current, primary_ret,
					      vcpu_state_ready);
		ret = 0;
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
		 * Take target vcpu out of waiter list and mark it as ready to
		 * run again.
		 */
		sl_lock(&to_vcpu->lock);
		to->mailbox.recv_waiter = to_vcpu->mailbox_next;
		to_vcpu->state = vcpu_state_ready;

		/* Return from HF_MAILBOX_RECEIVE. */
		to_vcpu->retval.force = true;
		to_vcpu->retval.value = hf_mailbox_receive_return_encode(
			(struct hf_mailbox_receive_return){
				.vm_id = to->mailbox.recv_from_id,
				.size = size,
			});

		sl_unlock(&to_vcpu->lock);

		vcpu = to_vcpu - to->vcpus;
	}

	/* Return to the primary VM directly or with a switch. */
	if (from->id == HF_PRIMARY_VM_ID) {
		ret = vcpu;
	} else {
		struct hf_vcpu_run_return primary_ret = {
			.code = HF_VCPU_RUN_WAKE_UP,
			.wake_up.vm_id = to->id,
			.wake_up.vcpu = vcpu,
		};

		*next = api_switch_to_primary(current, primary_ret,
					      vcpu_state_ready);
		ret = 0;
	}

out:
	sl_unlock(&to->lock);

	return ret;
}

/**
 * Receives a message from the mailbox. If one isn't available, this function
 * can optionally block the caller until one becomes available.
 *
 * No new messages can be received until the mailbox has been cleared.
 */
struct hf_mailbox_receive_return api_mailbox_receive(bool block,
						     struct vcpu *current,
						     struct vcpu **next)
{
	struct vm *vm = current->vm;
	struct hf_mailbox_receive_return ret = {
		.vm_id = HF_INVALID_VM_ID,
	};

	/*
	 * The primary VM will receive messages as a status code from running
	 * vcpus and must not call this function.
	 */
	if (vm->id == HF_PRIMARY_VM_ID) {
		return ret;
	}

	sl_lock(&vm->lock);

	/* Return pending messages without blocking. */
	if (vm->mailbox.state == mailbox_state_received) {
		vm->mailbox.state = mailbox_state_read;
		ret.vm_id = vm->mailbox.recv_from_id;
		ret.size = vm->mailbox.recv_bytes;
		goto out;
	}

	/* No pending message so fail if not allowed to block. */
	if (!block) {
		goto out;
	}

	sl_lock(&current->lock);

	/* Push vcpu into waiter list. */
	current->mailbox_next = vm->mailbox.recv_waiter;
	vm->mailbox.recv_waiter = current;
	sl_unlock(&current->lock);

	/* Switch back to primary vm to block. */
	{
		struct hf_vcpu_run_return run_return = {
			.code = HF_VCPU_RUN_WAIT_FOR_INTERRUPT,
		};

		*next = api_switch_to_primary(current, run_return,
					      vcpu_state_blocked_mailbox);
	}
out:
	sl_unlock(&vm->lock);

	return ret;
}

/**
 * Clears the caller's mailbox so that a new message can be received. The caller
 * must have copied out all data they wish to preserve as new messages will
 * overwrite the old and will arrive asynchronously.
 */
int64_t api_mailbox_clear(const struct vcpu *current)
{
	struct vm *vm = current->vm;
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

/**
 * Enables or disables a given interrupt ID for the calling vCPU.
 *
 * Returns 0 on success, or -1 if the intid is invalid.
 */
int64_t api_enable_interrupt(uint32_t intid, bool enable, struct vcpu *current)
{
	uint32_t intid_index = intid / INTERRUPT_REGISTER_BITS;
	uint32_t intid_mask = 1u << (intid % INTERRUPT_REGISTER_BITS);

	if (intid >= HF_NUM_INTIDS) {
		return -1;
	}

	sl_lock(&current->lock);
	if (enable) {
		/*
		 * If it is pending and was not enabled before, increment the
		 * count.
		 */
		if (current->interrupts.interrupt_pending[intid_index] &
		    ~current->interrupts.interrupt_enabled[intid_index] &
		    intid_mask) {
			current->interrupts.enabled_and_pending_count++;
		}
		current->interrupts.interrupt_enabled[intid_index] |=
			intid_mask;
	} else {
		/*
		 * If it is pending and was enabled before, decrement the count.
		 */
		if (current->interrupts.interrupt_pending[intid_index] &
		    current->interrupts.interrupt_enabled[intid_index] &
		    intid_mask) {
			current->interrupts.enabled_and_pending_count--;
		}
		current->interrupts.interrupt_enabled[intid_index] &=
			~intid_mask;
	}

	sl_unlock(&current->lock);
	return 0;
}

/**
 * Returns the ID of the next pending interrupt for the calling vCPU, and
 * acknowledges it (i.e. marks it as no longer pending). Returns
 * HF_INVALID_INTID if there are no pending interrupts.
 */
uint32_t api_get_and_acknowledge_interrupt(struct vcpu *current)
{
	uint8_t i;
	uint32_t first_interrupt = HF_INVALID_INTID;

	/*
	 * Find the first enabled and pending interrupt ID, return it, and
	 * deactivate it.
	 */
	sl_lock(&current->lock);
	for (i = 0; i < HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS; ++i) {
		uint32_t enabled_and_pending =
			current->interrupts.interrupt_enabled[i] &
			current->interrupts.interrupt_pending[i];

		if (enabled_and_pending != 0) {
			uint8_t bit_index = ctz(enabled_and_pending);
			/*
			 * Mark it as no longer pending and decrement the count.
			 */
			current->interrupts.interrupt_pending[i] &=
				~(1u << bit_index);
			current->interrupts.enabled_and_pending_count--;
			first_interrupt =
				i * INTERRUPT_REGISTER_BITS + bit_index;
			break;
		}
	}

	sl_unlock(&current->lock);
	return first_interrupt;
}

/**
 * Returns whether the current vCPU is allowed to inject an interrupt into the
 * given VM and vCPU.
 */
static inline bool is_injection_allowed(uint32_t target_vm_id,
					struct vcpu *current)
{
	uint32_t current_vm_id = current->vm->id;

	/*
	 * The primary VM is allowed to inject interrupts into any VM. Secondary
	 * VMs are only allowed to inject interrupts into their own vCPUs.
	 */
	return current_vm_id == HF_PRIMARY_VM_ID ||
	       current_vm_id == target_vm_id;
}

/**
 * Injects a virtual interrupt of the given ID into the given target vCPU.
 * This doesn't cause the vCPU to actually be run immediately; it will be taken
 * when the vCPU is next run, which is up to the scheduler.
 *
 * Returns:
 *  - -1 on failure because the target VM or vCPU doesn't exist, the interrupt
 *    ID is invalid, or the current VM is not allowed to inject interrupts to
 *    the target VM.
 *  - 0 on success if no further action is needed.
 *  - 1 if it was called by the primary VM and the primary VM now needs to wake
 *    up or kick the target vCPU.
 */
int64_t api_inject_interrupt(uint32_t target_vm_id, uint32_t target_vcpu_idx,
			     uint32_t intid, struct vcpu *current,
			     struct vcpu **next)
{
	uint32_t intid_index = intid / INTERRUPT_REGISTER_BITS;
	uint32_t intid_mask = 1u << (intid % INTERRUPT_REGISTER_BITS);
	struct vcpu *target_vcpu;
	struct vm *target_vm = vm_get(target_vm_id);
	bool need_vm_lock;
	int64_t ret = 0;

	if (intid >= HF_NUM_INTIDS) {
		return -1;
	}

	if (target_vm == NULL) {
		return -1;
	}

	if (target_vcpu_idx >= target_vm->vcpu_count) {
		/* The requested vcpu must exist. */
		return -1;
	}

	if (!is_injection_allowed(target_vm_id, current)) {
		return -1;
	}

	target_vcpu = &target_vm->vcpus[target_vcpu_idx];

	dlog("Injecting IRQ %d for VM %d VCPU %d from VM %d VCPU %d\n", intid,
	     target_vm_id, target_vcpu_idx, current->vm->id, current->cpu->id);

	sl_lock(&target_vcpu->lock);
	/*
	 * If we need the target_vm lock we need to release the target_vcpu lock
	 * first to maintain the correct order of locks. In-between releasing
	 * and acquiring it again the state of the vCPU could change in such a
	 * way that we don't actually need to touch the target_vm after all, but
	 * that's alright: we'll take the target_vm lock anyway, but it's safe,
	 * just perhaps a little slow in this unusual case. The reverse is not
	 * possible: if need_vm_lock is false, we don't release the target_vcpu
	 * lock until we are done, so nothing should change in such as way that
	 * we need the VM lock after all.
	 */
	need_vm_lock =
		(target_vcpu->interrupts.interrupt_enabled[intid_index] &
		 ~target_vcpu->interrupts.interrupt_pending[intid_index] &
		 intid_mask) &&
		target_vcpu->state == vcpu_state_blocked_mailbox;
	if (need_vm_lock) {
		sl_unlock(&target_vcpu->lock);
		sl_lock(&target_vm->lock);
		sl_lock(&target_vcpu->lock);
	}

	/*
	 * We only need to change state and (maybe) trigger a virtual IRQ if it
	 * is enabled and was not previously pending. Otherwise we can skip
	 * everything except setting the pending bit.
	 *
	 * If you change this logic make sure to update the need_vm_lock logic
	 * above to match.
	 */
	if (!(target_vcpu->interrupts.interrupt_enabled[intid_index] &
	      ~target_vcpu->interrupts.interrupt_pending[intid_index] &
	      intid_mask)) {
		goto out;
	}

	/* Increment the count. */
	target_vcpu->interrupts.enabled_and_pending_count++;

	/*
	 * Only need to update state if there was not already an
	 * interrupt enabled and pending.
	 */
	if (target_vcpu->interrupts.enabled_and_pending_count != 1) {
		goto out;
	}

	if (target_vcpu->state == vcpu_state_blocked_interrupt) {
		target_vcpu->state = vcpu_state_ready;
	} else if (target_vcpu->state == vcpu_state_blocked_mailbox) {
		/*
		 * If you change this logic make sure to update the need_vm_lock
		 * logic above to match.
		 */
		target_vcpu->state = vcpu_state_ready;

		/* Take target vCPU out of mailbox recv_waiter list. */
		/*
		 * TODO: Consider using a doubly-linked list for
		 * the receive waiter list to avoid the linear
		 * search here.
		 */
		struct vcpu **previous_next_pointer =
			&target_vm->mailbox.recv_waiter;
		while (*previous_next_pointer != NULL &&
		       *previous_next_pointer != target_vcpu) {
			/*
			 * TODO(qwandor): Do we need to lock the vCPUs somehow
			 * while we walk the linked list, or is the VM lock
			 * enough?
			 */
			previous_next_pointer =
				&(*previous_next_pointer)->mailbox_next;
		}

		if (*previous_next_pointer == NULL) {
			dlog("Target VCPU state is vcpu_state_blocked_mailbox "
			     "but is not in VM mailbox waiter list. This "
			     "should never happen.\n");
		} else {
			*previous_next_pointer = target_vcpu->mailbox_next;
		}
	}

	if (current->vm->id == HF_PRIMARY_VM_ID) {
		/*
		 * If the call came from the primary VM, let it know that it
		 * should run or kick the target vCPU.
		 */
		ret = 1;
	} else if (current != target_vcpu) {
		/*
		 * Switch to the primary so that it can switch to the target, or
		 * kick it if it is already running on a different physical CPU.
		 */
		struct hf_vcpu_run_return ret = {
			.code = HF_VCPU_RUN_WAKE_UP,
			.wake_up.vm_id = target_vm_id,
			.wake_up.vcpu = target_vcpu_idx,
		};

		*next = api_switch_to_primary(current, ret, vcpu_state_ready);
	}

out:
	/* Either way, make it pending. */
	target_vcpu->interrupts.interrupt_pending[intid_index] |= intid_mask;

	sl_unlock(&target_vcpu->lock);
	if (need_vm_lock) {
		sl_unlock(&target_vm->lock);
	}

	return ret;
}
