#include "hf/vm.h"

#include "hf/api.h"
#include "hf/cpu.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

static struct vm vms[MAX_VMS];
static uint32_t vm_count;

bool vm_init(uint32_t vcpu_count, struct vm **new_vm)
{
	uint32_t i;
	struct vm *vm;

	if (vm_count >= MAX_VMS) {
		return false;
	}

	vm = &vms[vm_count];

	memset(vm, 0, sizeof(*vm));

	vm->id = vm_count;
	vm->vcpu_count = vcpu_count;
	vm->rpc.state = rpc_state_idle;

	/* Do basic initialization of vcpus. */
	for (i = 0; i < vcpu_count; i++) {
		vcpu_init(&vm->vcpus[i], vm);
	}

	++vm_count;
	*new_vm = vm;

	return mm_ptable_init(&vm->ptable, 0);
}

uint32_t vm_get_count(void)
{
	return vm_count;
}

struct vm *vm_get(uint32_t id)
{
	/* Ensure the VM is initialized. */
	if (id >= vm_count) {
		return NULL;
	}

	return &vms[id];
}

/* TODO: Shall we use index or id here? */
void vm_start_vcpu(struct vm *vm, size_t index, ipaddr_t entry, size_t arg)
{
	struct vcpu *vcpu = &vm->vcpus[index];
	if (index < vm->vcpu_count) {
		arch_regs_init(&vcpu->regs, entry, arg);
		vcpu_on(vcpu);
	}
}

void vm_set_current(struct vm *vm)
{
	arch_cpu_update(vm->id == HF_PRIMARY_VM_ID);
	arch_mm_set_vm(vm->id, vm->ptable.table);
}
