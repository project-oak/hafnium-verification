#ifndef _API_H
#define _API_H

#include "cpu.h"
#include "vm.h"

/* TODO: Can we hide these? */
extern struct vm secondary_vm[MAX_VMS];
extern uint32_t secondary_vm_count;
extern struct vm primary_vm;

struct vcpu *api_switch_to_primary(size_t primary_retval,
				   enum vcpu_state secondary_state);

int32_t api_vm_get_count(void);
int32_t api_vcpu_get_count(uint32_t vm_idx);
int32_t api_vcpu_run(uint32_t vm_idx, uint32_t vcpu_idx, struct vcpu **next);
struct vcpu *api_wait_for_interrupt(void);
int32_t api_vm_configure(paddr_t send, paddr_t recv);

int32_t api_rpc_request(uint32_t vm_idx, size_t size);
int32_t api_rpc_read_request(bool block, struct vcpu **next);
int32_t api_rpc_reply(size_t size, bool ack, struct vcpu **next);
int32_t api_rpc_ack(void);

#endif /* _API_H */
