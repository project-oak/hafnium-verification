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

#include <stdatomic.h>

#include "hf/arch/types.h"

#include "hf/cpu.h"
#include "hf/list.h"
#include "hf/mm.h"
#include "hf/mpool.h"

#include "vmapi/hf/spci.h"

#define MAX_SMCS 32
#define LOG_BUFFER_SIZE 256

/**
 * The state of an RX buffer.
 *
 * EMPTY is the initial state. The follow state transitions are possible:
 * * EMPTY → RECEIVED: message sent to the VM.
 * * RECEIVED → READ: secondary VM returns from SPCI_MSG_WAIT or
 *   SPCI_MSG_POLL, or primary VM returns from SPCI_RUN with an SPCI_MSG_SEND
 *   where the receiver is itself.
 * * READ → EMPTY: VM called SPCI_RX_RELEASE.
 */
enum mailbox_state {
	/** There is no message in the mailbox. */
	MAILBOX_STATE_EMPTY,

	/** There is a message in the mailbox that is waiting for a reader. */
	MAILBOX_STATE_RECEIVED,

	/** There is a message in the mailbox that has been read. */
	MAILBOX_STATE_READ,
};

struct wait_entry {
	/** The VM that is waiting for a mailbox to become writable. */
	struct vm *waiting_vm;

	/**
	 * Links used to add entry to a VM's waiter_list. This is protected by
	 * the notifying VM's lock.
	 */
	struct list_entry wait_links;

	/**
	 * Links used to add entry to a VM's ready_list. This is protected by
	 * the waiting VM's lock.
	 */
	struct list_entry ready_links;
};

struct mailbox {
	enum mailbox_state state;
	void *recv;
	const void *send;

	/** The ID of the VM which sent the message currently in `recv`. */
	spci_vm_id_t recv_sender;

	/** The size of the message currently in `recv`. */
	uint32_t recv_size;

	/**
	 * The SPCI function ID to use to deliver the message currently in
	 * `recv`.
	 */
	uint32_t recv_func;

	/**
	 * List of wait_entry structs representing VMs that want to be notified
	 * when the mailbox becomes writable. Once the mailbox does become
	 * writable, the entry is removed from this list and added to the
	 * waiting VM's ready_list.
	 */
	struct list_entry waiter_list;

	/**
	 * List of wait_entry structs representing VMs whose mailboxes became
	 * writable since the owner of the mailbox registers for notification.
	 */
	struct list_entry ready_list;
};

struct smc_whitelist {
	uint32_t smcs[MAX_SMCS];
	uint16_t smc_count;
	bool permissive;
};

struct vm {
	spci_vm_id_t id;
	struct smc_whitelist smc_whitelist;

	/** See api.c for the partial ordering on locks. */
	struct spinlock lock;
	spci_vcpu_count_t vcpu_count;
	struct vcpu vcpus[MAX_CPUS];
	struct mm_ptable ptable;
	struct mailbox mailbox;
	char log_buffer[LOG_BUFFER_SIZE];
	uint16_t log_buffer_length;

	/**
	 * Wait entries to be used when waiting on other VM mailboxes. See
	 * comments on `struct wait_entry` for the lock discipline of these.
	 */
	struct wait_entry wait_entries[MAX_VMS];

	atomic_bool aborting;

	/** Arch-specific VM information. */
	struct arch_vm arch;
};

/** Encapsulates a VM whose lock is held. */
struct vm_locked {
	struct vm *vm;
};

/** Container for two vm_locked structures */
struct two_vm_locked {
	struct vm_locked vm1;
	struct vm_locked vm2;
};

struct vm *vm_init(spci_vm_id_t id, spci_vcpu_count_t vcpu_count,
		   struct mpool *ppool);
bool vm_init_next(spci_vcpu_count_t vcpu_count, struct mpool *ppool,
		  struct vm **new_vm);
spci_vm_count_t vm_get_count(void);
struct vm *vm_find(spci_vm_id_t id);
struct vm_locked vm_lock(struct vm *vm);
struct two_vm_locked vm_lock_both(struct vm *vm1, struct vm *vm2);
void vm_unlock(struct vm_locked *locked);
struct vcpu *vm_get_vcpu(struct vm *vm, spci_vcpu_index_t vcpu_index);
struct wait_entry *vm_get_wait_entry(struct vm *vm, spci_vm_id_t for_vm);
spci_vm_id_t vm_id_for_wait_entry(struct vm *vm, struct wait_entry *entry);

bool vm_identity_map(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
		     uint32_t mode, struct mpool *ppool, ipaddr_t *ipa);
bool vm_identity_prepare(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
			 uint32_t mode, struct mpool *ppool);
void vm_identity_commit(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
			uint32_t mode, struct mpool *ppool, ipaddr_t *ipa);
bool vm_unmap(struct vm_locked vm_locked, paddr_t begin, paddr_t end,
	      struct mpool *ppool);
bool vm_unmap_hypervisor(struct vm_locked vm_locked, struct mpool *ppool);
