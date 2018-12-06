/*
 * Copyright 2018 Google LLC
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

#include "hf/cpu.h"
#include "hf/mm.h"

enum mailbox_state {
	/** There is no message in the mailbox. */
	mailbox_state_empty,

	/** There is a message in the mailbox that is waiting for a reader. */
	mailbox_state_received,

	/** There is a message in the mailbox that has been read. */
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
	/** See api.c for the partial ordering on locks. */
	struct spinlock lock;
	uint32_t vcpu_count;
	struct vcpu vcpus[MAX_CPUS];
	struct mm_ptable ptable;
	struct mailbox mailbox;
};

bool vm_init(uint32_t vcpu_count, struct vm **new_vm);
uint32_t vm_get_count(void);
struct vm *vm_get(uint32_t id);
void vm_start_vcpu(struct vm *vm, size_t index, ipaddr_t entry, uintreg_t arg);
