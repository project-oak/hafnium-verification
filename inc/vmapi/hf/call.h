#ifndef _VMAPI_HF_HVC_H
#define _VMAPI_HF_HVC_H

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

/* Return values for vcpu_run() hypervisor call. */
#define HF_VCPU_YIELD              0x00
#define HF_VCPU_WAIT_FOR_INTERRUPT 0x01
#define HF_VCPU_WAKE_UP            0x02
#define HF_VCPU_RESPONSE_READY     0x03

/* TODO: Define constants below according to spec. */
#define HF_VCPU_RUN         0xff00
#define HF_VM_GET_COUNT     0xff01
#define HF_VCPU_GET_COUNT   0xff02
#define HF_VM_CONFIGURE     0xff03
#define HF_RPC_REQUEST      0xff04
#define HF_RPC_READ_REQUEST 0xff05
#define HF_RPC_ACK          0xff06
#define HF_RPC_REPLY        0xff07

/* clang-format on */

/**
 * This function must be implemented to trigger the architecture specific
 * mechanism to call to the hypervisor.
 */
size_t hf_call(size_t arg0, size_t arg1, size_t arg2, size_t arg3);

/**
 * Runs the given vcpu of the given vm.
 */
static inline int32_t hf_vcpu_run(uint32_t vm_idx, uint32_t vcpu_idx)
{
	return hf_call(HF_VCPU_RUN, vm_idx, vcpu_idx, 0);
}

/**
 * Returns the number of secondary VMs.
 */
static inline int32_t hf_vm_get_count(void)
{
	return hf_call(HF_VM_GET_COUNT, 0, 0, 0);
}

/**
 * Returns the number of VCPUs configured in the given secondary VM.
 */
static inline int32_t hf_vcpu_get_count(uint32_t vm_idx)
{
	return hf_call(HF_VCPU_GET_COUNT, vm_idx, 0, 0);
}

/**
 * Configures the pages to send/receive data through. The pages must not be
 * shared.
 */
static inline int32_t hf_vm_configure(hf_ipaddr_t send, hf_ipaddr_t recv)
{
	return hf_call(HF_VM_CONFIGURE, send, recv, 0);
}

/**
 * Called by the primary VM to send an RPC request to a secondary VM. Data is
 * copied from the caller's send buffer to the destination's receive buffer.
 */
static inline int32_t hf_rpc_request(uint32_t vm_idx, size_t size)
{
	return hf_call(HF_RPC_REQUEST, vm_idx, size, 0);
}

/**
 * Called by the primary VM to read a request sent from a previous call to
 * api_rpc_request. If one isn't available, this function can optionally block
 * the caller until one becomes available.
 *
 * Once the caller has completed handling a request, it must indicate it by
 * either calling api_rpc_reply or api_rpc_ack. No new requests can be accepted
 * until the current one is acknowledged.
 */
static inline int32_t hf_rpc_read_request(bool block)
{
	return hf_call(HF_RPC_READ_REQUEST, block, 0, 0);
}

/**
 * Acknowledges that either a request or a reply has been received and handled.
 * After this call completes, the caller will be able to receive additional
 * requests or replies.
 */
static inline int32_t hf_rpc_ack(void)
{
	return hf_call(HF_RPC_ACK, 0, 0, 0);
}

/**
 * Called by a secondary VM to send a reply to the primary VM. Data is copied
 * from the caller's send buffer to the destination's receive buffer.
 *
 * It can optionally acknowledge the pending request.
 */
static inline int32_t hf_rpc_reply(size_t size, bool ack)
{
	return hf_call(HF_RPC_REPLY, size, ack, 0);
}

#endif /* _VMAPI_HF_HVC_H */
