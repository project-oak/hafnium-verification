#include "vm.h"

#include "cpu.h"

void vm_init(struct vm *vm, uint32_t vcpu_count)
{
	uint32_t i;

	vm->vcpu_count = vcpu_count;

	/* Do basic initialization of vcpus. */
	for (i = 0; i < vcpu_count; i++) {
		vcpu_init(vm->vcpus + i, vm);
	}

	arch_vptable_init(&vm->page_table);
}

/* TODO: Shall we use index or id here? */
void vm_start_vcpu(struct vm *vm, size_t index, size_t entry, size_t arg,
		   bool is_primary)
{
	struct vcpu *vcpu = vm->vcpus + index;
	if (index < vm->vcpu_count) {
		arch_regs_init(&vcpu->regs, entry, arg, is_primary);
		vcpu_on(vcpu);
	}
}
