#include "hf/api.h"

#include <assert.h>

#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

static_assert(HF_RPC_REQUEST_MAX_SIZE == PAGE_SIZE,
	      "Currently, a page is mapped for the send and receive buffers so "
	      "the maximum request is the size of a page.");

/**
 * Switches the physical CPU back to the corresponding vcpu of the primary VM.
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
	 * Inidicate to primary VM that this vcpu blocked waiting for an
	 * interrupt.
	 */
	arch_regs_set_retval(&next->regs, primary_retval);

	/* Mark the vcpu as waiting. */
	sl_lock(&vcpu->lock);
	vcpu->state = secondary_state;
	sl_unlock(&vcpu->lock);

	return next;
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
		ret = HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT, 0);
	} else {
		vcpu->state = vcpu_state_running;
		vm_set_current(vm);
		*next = vcpu;
		ret = HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_YIELD, 0);
	}
	sl_unlock(&vcpu->lock);

	return ret;

fail:
	return HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT, 0);
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
	if (vm->rpc.send || vm->rpc.recv) {
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
	vm->rpc.send = mm_identity_map(pa_send_begin, pa_send_end, MM_MODE_R);
	if (!vm->rpc.send) {
		ret = -1;
		goto exit;
	}

	/*
	 * Map the receive page as writable in the hypervisor address space. On
	 * failure, unmap the send page before returning.
	 */
	vm->rpc.recv = mm_identity_map(pa_recv_begin, pa_recv_end, MM_MODE_W);
	if (!vm->rpc.recv) {
		vm->rpc.send = NULL;
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
 * Sends an RPC request from the primary VM to a secondary VM. Data is copied
 * from the caller's send buffer to the destination's receive buffer.
 */
int64_t api_rpc_request(uint32_t vm_id, size_t size)
{
	struct vm *from = cpu()->current->vm;
	struct vm *to;
	const void *from_buf;
	int64_t ret;

	/* Basic argument validation. */
	if (size > HF_RPC_REQUEST_MAX_SIZE) {
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

	/* Only the primary VM can make calls. */
	if (from->id != HF_PRIMARY_VM_ID) {
		return -1;
	}

	/*
	 * Check that the sender has configured its send buffer. It is safe to
	 * use from_buf after releasing the lock because the buffer cannot be
	 * modified once it's configured.
	 */
	sl_lock(&from->lock);
	from_buf = from->rpc.send;
	sl_unlock(&from->lock);
	if (!from_buf) {
		return -1;
	}

	sl_lock(&to->lock);

	if (to->rpc.state != rpc_state_idle || !to->rpc.recv) {
		/* Fail if the target isn't currently ready to receive data. */
		ret = -1;
	} else {
		/* Copy data. */
		memcpy(to->rpc.recv, from_buf, size);
		to->rpc.recv_bytes = size;

		if (!to->rpc.recv_waiter) {
			to->rpc.state = rpc_state_pending;
			ret = to->vcpu_count;
		} else {
			struct vcpu *to_vcpu = to->rpc.recv_waiter;

			to->rpc.state = rpc_state_inflight;

			/*
			 * Take target vcpu out of waiter list and mark as ready
			 * to run again.
			 */
			sl_lock(&to_vcpu->lock);
			to->rpc.recv_waiter = to_vcpu->rpc_next;
			to_vcpu->state = vcpu_state_ready;
			arch_regs_set_retval(&to_vcpu->regs, size);
			sl_unlock(&to_vcpu->lock);

			ret = to_vcpu - to->vcpus;
		}
	}

	sl_unlock(&to->lock);

	return ret;
}

/**
 * Reads a request sent from a previous call to api_rpc_request. If one isn't
 * available, this function can optionally block the caller until one becomes
 * available.
 *
 * Once the caller has completed handling a request, it must indicate it by
 * either calling api_rpc_reply or api_rpc_ack. No new requests can be accepted
 * until the current one is acknowledged.
 */
int64_t api_rpc_read_request(bool block, struct vcpu **next)
{
	struct vcpu *vcpu = cpu()->current;
	struct vm *vm = vcpu->vm;
	struct vm *primary = vm_get(HF_PRIMARY_VM_ID);
	int64_t ret;

	/* Only the secondary VMs can receive calls. */
	if (vm->id == HF_PRIMARY_VM_ID) {
		return -1;
	}

	sl_lock(&vm->lock);
	if (vm->rpc.state == rpc_state_pending) {
		ret = vm->rpc.recv_bytes;
		vm->rpc.state = rpc_state_inflight;
	} else if (!block) {
		ret = -1;
	} else {
		sl_lock(&vcpu->lock);
		vcpu->state = vcpu_state_blocked_rpc;

		/* Push vcpu into waiter list. */
		vcpu->rpc_next = vm->rpc.recv_waiter;
		vm->rpc.recv_waiter = vcpu;
		sl_unlock(&vcpu->lock);

		/* Switch back to primary vm. */
		*next = &primary->vcpus[cpu_index(cpu())];
		vm_set_current(primary);

		/*
		 * Inidicate to primary VM that this vcpu blocked waiting for an
		 * interrupt.
		 */
		arch_regs_set_retval(
			&(*next)->regs,
			HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT,
					     0));
		ret = 0;
	}
	sl_unlock(&vm->lock);

	return ret;
}

/**
 * Sends a reply from a secondary VM to the primary VM. Data is copied from the
 * caller's send buffer to the destination's receive buffer.
 *
 * It can optionally acknowledge the pending request.
 */
int64_t api_rpc_reply(size_t size, bool ack, struct vcpu **next)
{
	struct vm *from = cpu()->current->vm;
	struct vm *to;
	const void *from_buf;

	/* Basic argument validation. */
	if (size > PAGE_SIZE) {
		return -1;
	}

	/* Only the secondary VM can send responses. */
	if (from->id == HF_PRIMARY_VM_ID) {
		return -1;
	}

	/* Acknowledge the current pending request if requested. */
	if (ack) {
		api_rpc_ack();
	}

	/*
	 * Check that the sender has configured its send buffer. It is safe to
	 * use from_buf after releasing the lock because the buffer cannot be
	 * modified once it's configured.
	 */
	sl_lock(&from->lock);
	from_buf = from->rpc.send;
	sl_unlock(&from->lock);
	if (!from_buf) {
		return -1;
	}

	to = vm_get(HF_PRIMARY_VM_ID);
	sl_lock(&to->lock);

	if (to->rpc.state != rpc_state_idle || !to->rpc.recv) {
		/*
		 * Fail if the target isn't currently ready to receive a
		 * response.
		 */
		sl_unlock(&to->lock);
		return -1;
	}

	/* Copy data. */
	memcpy(to->rpc.recv, from_buf, size);
	to->rpc.recv_bytes = size;
	to->rpc.state = rpc_state_inflight;
	sl_unlock(&to->lock);

	/*
	 * Switch back to primary VM so that it is aware that a response was
	 * received. But we leave the current vcpu still runnable.
	 */
	*next = api_switch_to_primary(
		HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_RESPONSE_READY, size),
		vcpu_state_ready);

	return 0;
}

/**
 * Acknowledges that either a request or a reply has been received and handled.
 * After this call completes, the caller will be able to receive additional
 * requests or replies.
 */
int64_t api_rpc_ack(void)
{
	struct vm *vm = cpu()->current->vm;
	int64_t ret;

	sl_lock(&vm->lock);
	if (vm->rpc.state != rpc_state_inflight) {
		ret = -1;
	} else {
		ret = 0;
		vm->rpc.state = rpc_state_idle;
	}
	sl_unlock(&vm->lock);

	if (ret == 0) {
		/* TODO: Notify waiters, if any. */
	}

	return ret;
}

/**
 * Returns to the primary vm leaving the current vcpu ready to be scheduled
 * again.
 */
struct vcpu *api_yield(void)
{
	return api_switch_to_primary(HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_YIELD, 0),
				     vcpu_state_ready);
}

/**
 * Puts the current vcpu in wait for interrupt mode, and returns to the primary
 * vm.
 */
struct vcpu *api_wait_for_interrupt(void)
{
	return api_switch_to_primary(
		HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT, 0),
		vcpu_state_blocked_interrupt);
}
