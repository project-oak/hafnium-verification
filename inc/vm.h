#ifndef _VM_H
#define _VM_H

#include "cpu.h"
#include "mm.h"

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
	struct rpc rpc;
	struct mm_ptable ptable;
	uint32_t vcpu_count;
	struct vcpu vcpus[MAX_CPUS];
};

bool vm_init(struct vm *vm, uint32_t id, uint32_t vcpu_count);
void vm_start_vcpu(struct vm *vm, size_t index, size_t entry, size_t arg,
		   bool is_primary);
void vm_set_current(struct vm *vm);

#endif /* _VM_H */
