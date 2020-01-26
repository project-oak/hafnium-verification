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

#include "hf/cpu.h"
#include "hf/mpool.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"
#include "vmapi/hf/spci.h"

void api_init(struct mpool *ppool);
spci_vm_count_t api_vm_get_count(void);
spci_vcpu_count_t api_vcpu_get_count(spci_vm_id_t vm_id,
				     const struct vcpu *current);
void api_regs_state_saved(struct vcpu *vcpu);
int64_t api_mailbox_writable_get(const struct vcpu *current);
int64_t api_mailbox_waiter_get(spci_vm_id_t vm_id, const struct vcpu *current);
int64_t api_debug_log(char c, struct vcpu *current);

struct vcpu *api_preempt(struct vcpu *current);
struct vcpu *api_wait_for_interrupt(struct vcpu *current);
struct vcpu *api_vcpu_off(struct vcpu *current);
struct vcpu *api_abort(struct vcpu *current);
struct vcpu *api_wake_up(struct vcpu *current, struct vcpu *target_vcpu);

int64_t api_interrupt_enable(uint32_t intid, bool enable, struct vcpu *current);
uint32_t api_interrupt_get(struct vcpu *current);
int64_t api_interrupt_inject(spci_vm_id_t target_vm_id,
			     spci_vcpu_index_t target_vcpu_idx, uint32_t intid,
			     struct vcpu *current, struct vcpu **next);

struct spci_value api_spci_msg_send(spci_vm_id_t sender_vm_id,
				    spci_vm_id_t receiver_vm_id, uint32_t size,
				    uint32_t attributes, struct vcpu *current,
				    struct vcpu **next);
struct spci_value api_spci_msg_recv(bool block, struct vcpu *current,
				    struct vcpu **next);
struct spci_value api_spci_rx_release(struct vcpu *current, struct vcpu **next);
struct spci_value api_spci_rxtx_map(ipaddr_t send, ipaddr_t recv,
				    uint32_t page_count, struct vcpu *current,
				    struct vcpu **next);
void api_yield(struct vcpu *current, struct vcpu **next);
struct spci_value api_spci_version(void);
struct spci_value api_spci_id_get(const struct vcpu *current);
struct spci_value api_spci_features(uint32_t function_id);
struct spci_value api_spci_run(spci_vm_id_t vm_id, spci_vcpu_index_t vcpu_idx,
			       const struct vcpu *current, struct vcpu **next);
struct spci_value api_spci_mem_send(uint32_t share_func, ipaddr_t address,
				    uint32_t page_count,
				    uint32_t fragment_length, uint32_t length,
				    uint32_t cookie, struct vcpu *current,
				    struct vcpu **next);
