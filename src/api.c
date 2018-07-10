#include "api.h"

#include "arch_api.h"
#include "vm.h"

struct vm secondary_vm[MAX_VMS];
uint32_t secondary_vm_count;
struct vm primary_vm;

/**
 * Returns the number of VMs configured to run.
 */
int32_t api_vm_get_count(void)
{
	return secondary_vm_count;
}

/**
 * Returns the number of vcpus configured in the given VM.
 */
int32_t api_vcpu_get_count(uint32_t vm_idx)
{
	if (vm_idx >= secondary_vm_count)
		return -1;

	return secondary_vm[vm_idx].vcpu_count;
}

/**
 * Runs the given vcpu of the given vm.
 */
int32_t api_vcpu_run(uint32_t vm_idx, uint32_t vcpu_idx, struct vcpu **next)
{
	struct vm *vm = secondary_vm + vm_idx;
	struct vcpu *vcpu;

	/* Only the primary VM can switch vcpus. */
	if (cpu()->current->vm != &primary_vm)
		return HF_VCPU_WAIT_FOR_INTERRUPT;

	if (vm_idx >= secondary_vm_count)
		return HF_VCPU_WAIT_FOR_INTERRUPT;

	vcpu = vm->vcpus + vcpu_idx;
	if (vcpu_idx >= vm->vcpu_count || !vcpu->is_on)
		return HF_VCPU_WAIT_FOR_INTERRUPT;

	arch_set_vm_mm(&vm->page_table);
	*next = vcpu;

	return HF_VCPU_YIELD;
}

/**
 * Puts current vcpu in wait for interrupt mode, and returns to the primary
 * vm.
 */
struct vcpu *api_wait_for_interrupt(void)
{
	struct vcpu *vcpu = &primary_vm.vcpus[cpu_index(cpu())];

	/* Switch back to primary VM. */
	arch_set_vm_mm(&primary_vm.page_table);

	/*
	 * Inidicate to primary VM that this vcpu blocked waiting for an
	 * interrupt.
	 */
	arch_regs_set_retval(&vcpu->regs, HF_VCPU_WAIT_FOR_INTERRUPT);

	return vcpu;
}
