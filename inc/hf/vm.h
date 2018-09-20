#pragma once

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
	uint32_t id;
	struct spinlock lock;
	uint32_t vcpu_count;
	struct vcpu vcpus[MAX_CPUS];
	struct mm_ptable ptable;
	struct rpc rpc;
};

bool vm_init(uint32_t vcpu_count, struct vm **new_vm);
uint32_t vm_get_count(void);
struct vm *vm_get(uint32_t id);
void vm_start_vcpu(struct vm *vm, size_t index, ipaddr_t entry, size_t arg);
void vm_set_current(struct vm *vm);
