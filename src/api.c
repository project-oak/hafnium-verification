#include "api.h"

#include "std.h"
#include "vm.h"
#include "vmapi/hf/call.h"

struct vm secondary_vm[MAX_VMS];
uint32_t secondary_vm_count;
struct vm primary_vm;

/**
 * Switches the physical CPU back to the corresponding vcpu of the primary VM.
 */
struct vcpu *api_switch_to_primary(size_t primary_retval,
				   enum vcpu_state secondary_state)
{
	struct vcpu *vcpu = cpu()->current;
	struct vcpu *next = &primary_vm.vcpus[cpu_index(cpu())];

	/* Switch back to primary VM. */
	vm_set_current(&primary_vm);

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
int32_t api_vm_get_count(void)
{
	return secondary_vm_count;
}

/**
 * Returns the number of vcpus configured in the given VM.
 */
int32_t api_vcpu_get_count(uint32_t vm_idx)
{
	if (vm_idx >= secondary_vm_count) {
		return -1;
	}

	return secondary_vm[vm_idx].vcpu_count;
}

/**
 * Runs the given vcpu of the given vm.
 */
int32_t api_vcpu_run(uint32_t vm_idx, uint32_t vcpu_idx, struct vcpu **next)
{
	struct vm *vm;
	struct vcpu *vcpu;
	int32_t ret;

	/* Only the primary VM can switch vcpus. */
	if (cpu()->current->vm != &primary_vm) {
		return HF_VCPU_WAIT_FOR_INTERRUPT;
	}

	if (vm_idx >= secondary_vm_count) {
		return HF_VCPU_WAIT_FOR_INTERRUPT;
	}

	vm = secondary_vm + vm_idx;
	if (vcpu_idx >= vm->vcpu_count) {
		return HF_VCPU_WAIT_FOR_INTERRUPT;
	}

	vcpu = vm->vcpus + vcpu_idx;

	sl_lock(&vcpu->lock);
	if (vcpu->state != vcpu_state_ready) {
		ret = HF_VCPU_WAIT_FOR_INTERRUPT;
	} else {
		vcpu->state = vcpu_state_running;
		vm_set_current(vm);
		*next = vcpu;
		ret = HF_VCPU_YIELD;
	}
	sl_unlock(&vcpu->lock);

	return ret;
}

/**
 * Puts the current vcpu in wait for interrupt mode, and returns to the primary
 * vm.
 */
struct vcpu *api_wait_for_interrupt(void)
{
	return api_switch_to_primary(HF_VCPU_WAIT_FOR_INTERRUPT,
				     vcpu_state_blocked_interrupt);
}

/**
 * Configures the VM to send/receive data through the specified pages. The pages
 * must not be shared.
 */
int32_t api_vm_configure(ipaddr_t send, ipaddr_t recv)
{
	struct vm *vm = cpu()->current->vm;
	paddr_t pa_send_begin;
	paddr_t pa_send_end;
	paddr_t pa_recv_begin;
	paddr_t pa_recv_end;
	int32_t ret;

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
int32_t api_rpc_request(uint32_t vm_idx, size_t size)
{
	struct vm *from = cpu()->current->vm;
	struct vm *to;
	const void *from_buf;
	int32_t ret;

	/* Basic argument validation. */
	if (size > PAGE_SIZE || vm_idx >= secondary_vm_count) {
		return -1;
	}

	/* Only the primary VM can make calls. */
	if (from != &primary_vm) {
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

	to = secondary_vm + vm_idx;
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
			ret = 0;
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

			ret = to_vcpu - to->vcpus + 1;
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
int32_t api_rpc_read_request(bool block, struct vcpu **next)
{
	struct vcpu *vcpu = cpu()->current;
	struct vm *vm = vcpu->vm;
	int32_t ret;

	/* Only the secondary VMs can receive calls. */
	if (vm == &primary_vm) {
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
		*next = &primary_vm.vcpus[cpu_index(cpu())];
		vm_set_current(&primary_vm);

		/*
		 * Inidicate to primary VM that this vcpu blocked waiting for an
		 * interrupt.
		 */
		arch_regs_set_retval(&(*next)->regs,
				     HF_VCPU_WAIT_FOR_INTERRUPT);
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
int32_t api_rpc_reply(size_t size, bool ack, struct vcpu **next)
{
	struct vm *from = cpu()->current->vm;
	struct vm *to;
	const void *from_buf;
	/* Basic argument validation. */
	if (size > PAGE_SIZE) {
		return -1;
	}

	/* Only the secondary VM can send responses. */
	if (from == &primary_vm) {
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

	to = &primary_vm;
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
	*next = api_switch_to_primary((size << 8) | HF_VCPU_RESPONSE_READY,
				      vcpu_state_ready);

	return 0;
}

/**
 * Acknowledges that either a request or a reply has been received and handled.
 * After this call completes, the caller will be able to receive additional
 * requests or replies.
 */
int32_t api_rpc_ack(void)
{
	struct vm *vm = cpu()->current->vm;
	int32_t ret;

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
