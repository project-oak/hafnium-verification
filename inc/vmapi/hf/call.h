#pragma once

#if defined(__linux__) && defined(__KERNEL__)

#include <linux/types.h>

typedef phys_addr_t hf_ipaddr_t;

#else

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef uintptr_t hf_ipaddr_t;

#endif

/* Keep macro alignment */
/* clang-format off */

/* TODO: Define constants below according to spec. */
#define HF_VCPU_RUN         0xff00
#define HF_VM_GET_COUNT     0xff01
#define HF_VCPU_GET_COUNT   0xff02
#define HF_VM_CONFIGURE     0xff03
#define HF_MAILBOX_SEND     0xff04
#define HF_MAILBOX_RECEIVE  0xff05
#define HF_MAILBOX_CLEAR    0xff06

/* The ID of the primary VM which is responsile for scheduling. */
#define HF_PRIMARY_VM_ID 0

/* Return codes for hf_vcpu_run(). */
#define HF_VCPU_RUN_YIELD              0x00
#define HF_VCPU_RUN_WAIT_FOR_INTERRUPT 0x01
#define HF_VCPU_RUN_WAKE_UP            0x02
#define HF_VCPU_RUN_MESSAGE            0x03

/* Construct and destruct the hf_vcpu_run() response. */
#define HF_VCPU_RUN_RESPONSE(code, vm_id, data)               \
	((code & 0xff) | ((uint64_t)(vm_id & 0xffff) << 16) | \
	 ((uint64_t)data << 32))
#define HF_VCPU_RUN_CODE(ret) (ret & 0xff)
#define HF_VCPU_RUN_VM_ID(ret) ((ret >> 16) & 0xffff)
#define HF_VCPU_RUN_DATA(ret) (ret >> 32)

/* Construct and destruct the hf_mailbox_receive() response. */
#define HF_MAILBOX_RECEIVE_RESPONSE(vm_id, size) \
	((vm_id & 0xffff) | ((uint64_t)size << 32))
#define HF_MAILBOX_RECEIVE_VM_ID(ret) (ret & 0xffff)
#define HF_MAILBOX_RECEIVE_SIZE(ret) (ret >> 32)

#define HF_MAILBOX_SIZE 4096

#define HF_INVALID_VM_ID 0xffff
#define HF_INVALID_VCPU  0xffff

/* clang-format on */

/**
 * This function must be implemented to trigger the architecture specific
 * mechanism to call to the hypervisor.
 */
int64_t hf_call(size_t arg0, size_t arg1, size_t arg2, size_t arg3);

/**
 * Runs the given vcpu of the given vm.
 */
static inline int64_t hf_vcpu_run(uint32_t vm_id, uint32_t vcpu_idx)
{
	return hf_call(HF_VCPU_RUN, vm_id, vcpu_idx, 0);
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
 * Configures the pages to send/receive data through. The pages must not be
 * shared.
 */
static inline int64_t hf_vm_configure(hf_ipaddr_t send, hf_ipaddr_t recv)
{
	return hf_call(HF_VM_CONFIGURE, send, recv, 0);
}

/**
 * Copies data from the sender's send buffer to the recipient's receive buffer.
 */
static inline int64_t hf_mailbox_send(uint32_t vm_id, size_t size)
{
	return hf_call(HF_MAILBOX_SEND, vm_id, size, 0);
}

/**
 * Called by secondary VMs to receive a message. The call can optionally block
 * until a message is received.
 *
 * The mailbox must be cleared before a new message can be received.
 */
static inline int64_t hf_mailbox_receive(bool block)
{
	return hf_call(HF_MAILBOX_RECEIVE, block, 0, 0);
}

/**
 * Clears the mailbox so a new message can be received.
 */
static inline int64_t hf_mailbox_clear(void)
{
	return hf_call(HF_MAILBOX_CLEAR, 0, 0, 0);
}
