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

#pragma once

#include "hf/abi.h"
#include "hf/spci.h"
#include "hf/types.h"

/* Keep macro alignment */
/* clang-format off */

/* TODO: Define constants below according to spec. */
#define HF_VM_GET_ID            0xff00
#define HF_VM_GET_COUNT         0xff01
#define HF_VCPU_GET_COUNT       0xff02
#define HF_VCPU_RUN             0xff03
#define HF_VCPU_YIELD           0xff04
#define HF_VM_CONFIGURE         0xff05
#define HF_MAILBOX_CLEAR        0xff08
#define HF_MAILBOX_WRITABLE_GET 0xff09
#define HF_MAILBOX_WAITER_GET   0xff0a
#define HF_INTERRUPT_ENABLE     0xff0b
#define HF_INTERRUPT_GET        0xff0c
#define HF_INTERRUPT_INJECT     0xff0d
#define HF_SHARE_MEMORY         0xff0e

/** The amount of data that can be sent to a mailbox. */
#define HF_MAILBOX_SIZE 4096

/* clang-format on */

/**
 * This function must be implemented to trigger the architecture specific
 * mechanism to call to the hypervisor.
 */
int64_t hf_call(size_t arg0, size_t arg1, size_t arg2, size_t arg3);

/**
 * Returns the VM's own ID.
 */
static inline uint32_t hf_vm_get_id(void)
{
	return hf_call(HF_VM_GET_ID, 0, 0, 0);
}

/**
 * Returns the number of secondary VMs.
 */
static inline int64_t hf_vm_get_count(void)
{
	return hf_call(HF_VM_GET_COUNT, 0, 0, 0);
}

/**
 * Returns the number of VCPUs configured in the given secondary VM.
 */
static inline int64_t hf_vcpu_get_count(uint32_t vm_id)
{
	return hf_call(HF_VCPU_GET_COUNT, vm_id, 0, 0);
}

/**
 * Runs the given vcpu of the given vm.
 *
 * Returns an hf_vcpu_run_return struct telling the scheduler what to do next.
 */
static inline struct hf_vcpu_run_return hf_vcpu_run(uint32_t vm_id,
						    uint32_t vcpu_idx)
{
	return hf_vcpu_run_return_decode(
		hf_call(HF_VCPU_RUN, vm_id, vcpu_idx, 0));
}

/**
 * Hints that the vcpu is willing to yield its current use of the physical CPU.
 */
static inline void hf_vcpu_yield(void)
{
	hf_call(HF_VCPU_YIELD, 0, 0, 0);
}

/**
 * Configures the pages to send/receive data through. The pages must not be
 * shared.
 *
 * Returns:
 *  - -1 on failure.
 *  - 0 on success if no further action is needed.
 *  - 1 if it was called by the primary VM and the primary VM now needs to wake
 *    up or kick waiters.
 */
static inline int64_t hf_vm_configure(hf_ipaddr_t send, hf_ipaddr_t recv)
{
	return hf_call(HF_VM_CONFIGURE, send, recv, 0);
}

/**
 * Copies data from the sender's send buffer to the recipient's receive buffer.
 *
 * If the recipient's receive buffer is busy, it can optionally register the
 * caller to be notified when the recipient's receive buffer becomes available.
 *
 * Returns SPCI_SUCCESS if the message is sent, an error code otherwise:
 *  - INVALID_PARAMETER: one or more of the parameters do not conform.
 *  - BUSY: the message could not be delivered either because the mailbox
 *            was full or the target VM does not yet exist.
 */
static inline int64_t spci_msg_send(uint32_t attributes)
{
	return hf_call(SPCI_MSG_SEND_32, attributes, 0, 0);
}

/**
 * Called by secondary VMs to receive a message. The call can optionally block
 * until a message is received.
 *
 * If no message was received, the VM ID will be HF_INVALID_VM_ID.
 *
 * The mailbox must be cleared before a new message can be received.
 *
 * If no message is immediately available, `block` is true, and there are no
 * enabled and pending interrupts (irrespective of whether interrupts are
 * enabled globally), then this will block until a message is available or an
 * enabled interrupt becomes pending. This matches the behaviour of the WFI
 * instruction on aarch64, except that a message becoming available is also
 * treated like a wake-up event.
 */
static inline int32_t spci_msg_recv(int32_t attributes)
{
	return hf_call(SPCI_MSG_RECV_32, attributes, 0, 0);
}

/**
 * Clears the caller's mailbox so a new message can be received.
 *
 * Returns:
 *  - -1 on failure, if the mailbox hasn't been read.
 *  - 0 on success if no further action is needed.
 *  - 1 if it was called by the primary VM and the primary VM now needs to wake
 *    up or kick waiters. Waiters should be retrieved by calling
 *    hf_mailbox_waiter_get.
 */
static inline int64_t hf_mailbox_clear(void)
{
	return hf_call(HF_MAILBOX_CLEAR, 0, 0, 0);
}

/**
 * Retrieves the next VM whose mailbox became writable. For a VM to be notified
 * by this function, the caller must have called api_mailbox_send before with
 * the notify argument set to true, and this call must have failed because the
 * mailbox was not available.
 *
 * It should be called repeatedly to retrieve a list of VMs.
 *
 * Returns -1 if no VM became writable, or the id of the VM whose mailbox
 * became writable.
 */
static inline int64_t hf_mailbox_writable_get(void)
{
	return hf_call(HF_MAILBOX_WRITABLE_GET, 0, 0, 0);
}

/**
 * Retrieves the next VM waiting to be notified that the mailbox of the
 * specified VM became writable. Only primary VMs are allowed to call this.
 *
 * Returns -1 on failure or if there are no waiters; the VM id of the next
 * waiter otherwise.
 */
static inline int64_t hf_mailbox_waiter_get(uint32_t vm_id)
{
	return hf_call(HF_MAILBOX_WAITER_GET, vm_id, 0, 0);
}

/**
 * Enables or disables a given interrupt ID.
 *
 * Returns 0 on success, or -1 if the intid is invalid.
 */
static inline int64_t hf_interrupt_enable(uint32_t intid, bool enable)
{
	return hf_call(HF_INTERRUPT_ENABLE, intid, enable, 0);
}

/**
 * Gets the ID of the pending interrupt (if any) and acknowledge it.
 *
 * Returns HF_INVALID_INTID if there are no pending interrupts.
 */
static inline uint32_t hf_interrupt_get(void)
{
	return hf_call(HF_INTERRUPT_GET, 0, 0, 0);
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
static inline int64_t hf_interrupt_inject(uint32_t target_vm_id,
					  uint32_t target_vcpu_idx,
					  uint32_t intid)
{
	return hf_call(HF_INTERRUPT_INJECT, target_vm_id, target_vcpu_idx,
		       intid);
}

/**
 * Shares a region of memory with another VM.
 *
 * Returns 0 on success or -1 if the sharing was not allowed or failed.
 *
 * TODO: replace this with a better API once we have decided what that should
 *       look like.
 */
static inline int64_t hf_share_memory(uint32_t vm_id, hf_ipaddr_t addr,
				      size_t size, enum hf_share share)
{
	return hf_call(HF_SHARE_MEMORY, (((uint64_t)vm_id) << 32) | share, addr,
		       size);
}
