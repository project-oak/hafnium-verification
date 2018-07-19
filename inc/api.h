#ifndef _API_H
#define _API_H

#include "cpu.h"
#include "vm.h"

/* TODO: Can we hide these? */
extern struct vm secondary_vm[MAX_VMS];
extern uint32_t secondary_vm_count;
extern struct vm primary_vm;

int32_t api_vm_get_count(void);
int32_t api_vcpu_get_count(uint32_t vm_idx);
int32_t api_vcpu_run(uint32_t vm_idx, uint32_t vcpu_idx, struct vcpu **next);
struct vcpu *api_wait_for_interrupt(void);

#endif /* _API_H */
