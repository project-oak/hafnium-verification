#include "vm.h"

#include "cpu.h"

void vm_init(struct vm *vm, struct cpu *cpus)
{
	size_t i;

	/* Do basic initialization of vcpus. */
	for (i = 0; i < MAX_CPUS; i++) {
		vcpu_init(vm->vcpus + i, cpus + i, vm);
	}

	arch_vptable_init(&vm->page_table);
}

/* TODO: Shall we use index or id here? */
void vm_start_vcpu(struct vm *vm, size_t index, size_t entry, size_t arg)
{
	struct vcpu *vcpu = vm->vcpus + index;
	arch_regs_init(&vcpu->regs, entry, arg);
	vcpu_ready(vcpu);
	cpu_on(vcpu->cpu);
}
