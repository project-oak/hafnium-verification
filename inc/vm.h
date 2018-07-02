#ifndef _VM_H
#define _VM_H

#include "cpu.h"

struct vm {
	struct vcpu vcpus[MAX_CPUS];
	uint32_t vcpu_count;
	struct arch_page_table page_table;
};

void vm_init(struct vm *vm, uint32_t vcpu_count);
void vm_start_vcpu(struct vm *vm, size_t index, size_t entry, size_t arg,
		   bool is_primary);

#endif  /* _VM_H */
