#pragma once

#include "hf/cpu.h"
#include "hf/mm.h"

enum mailbox_state {
	/* There is no message in the mailbox. */
	mailbox_state_empty,

	/* There is a message in the mailbox that is waiting for a reader. */
	mailbox_state_received,

	/* There is a message in the mailbox that has been read. */
	mailbox_state_read,
};

struct mailbox {
	enum mailbox_state state;
	uint32_t recv_from_id;
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
	struct mailbox mailbox;
};

bool vm_init(uint32_t vcpu_count, struct vm **new_vm);
uint32_t vm_get_count(void);
struct vm *vm_get(uint32_t id);
void vm_start_vcpu(struct vm *vm, size_t index, ipaddr_t entry, size_t arg);
void vm_set_current(struct vm *vm);
