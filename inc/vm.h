#ifndef _VM_H
#define _VM_H

#include "cpu.h"

struct vm {
	struct vcpu vcpus[MAX_CPUS];
	struct arch_page_table page_table;
};

void vm_init(struct vm *vm, struct cpu *cpus);
void vm_start_vcpu(struct vm *vm, size_t index, size_t entry, size_t arg);

#endif  /* _VM_H */
