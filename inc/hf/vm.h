#ifndef _VM_H
#define _VM_H

#include "hf/cpu.h"
#include "hf/mm.h"

enum rpc_state {
	rpc_state_idle,
	rpc_state_pending,
	rpc_state_inflight,
};

struct rpc {
	enum rpc_state state;
	int16_t recv_bytes;
	void *recv;
	const void *send;
	struct vcpu *recv_waiter;
};

struct vm {
	struct spinlock lock;
	uint32_t vcpu_count;
	struct vcpu vcpus[MAX_CPUS];
	struct mm_ptable ptable;
	struct rpc rpc;
};

bool vm_init(struct vm *vm, uint32_t id, uint32_t vcpu_count);
void vm_start_vcpu(struct vm *vm, size_t index, ipaddr_t entry, size_t arg);
void vm_set_current(struct vm *vm);

#endif /* _VM_H */
