#pragma once

#include "hf/cpu.h"
#include "hf/vm.h"

int64_t api_vm_get_count(void);
int64_t api_vcpu_get_count(uint32_t vm_id);
int64_t api_vcpu_run(uint32_t vm_id, uint32_t vcpu_idx, struct vcpu **next);
int64_t api_vm_configure(ipaddr_t send, ipaddr_t recv);

int64_t api_mailbox_send(uint32_t vm_id, size_t size, struct vcpu **next);
int64_t api_mailbox_receive(bool block, struct vcpu **next);
int64_t api_mailbox_clear(void);

struct vcpu *api_wait_for_interrupt(void);
struct vcpu *api_yield(void);
