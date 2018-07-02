#include "cpu.h"
#include "dlog.h"
#include "vm.h"

#include "msr.h"

struct hvc_handler_return {
	long user_ret;
	struct vcpu *new;
};

void irq_current(void)
{
	dlog("IRQ from current\n");
	for (;;);
}

void sync_current_exception(uint64_t esr, uint64_t elr)
{
	dlog("Exception: esr=%#x, elr=%#x\n", esr, elr);
	for (;;);
}

/* TODO: Define constants below according to spec. */
#define HF_VCPU_RUN       0xff00
#define HF_VM_GET_COUNT   0xff01
#define HF_VCPU_GET_COUNT 0xff02

/* TODO: Move these decl elsewhere. */
extern struct vm secondary_vm[MAX_VMS];
extern uint32_t secondary_vm_count;
extern struct vm primary_vm;
extern struct cpu cpus[];

struct hvc_handler_return hvc_handler(size_t arg0, size_t arg1, size_t arg2,
				      size_t arg3)
{
	struct hvc_handler_return ret;

	ret.new = NULL;

	switch (arg0) {
	case 0x84000000: /* PSCI_VERSION */
		ret.user_ret = 2;
		break;

	case 0x84000006: /* PSCI_MIGRATE */
		ret.user_ret = 2;
		break;

	case HF_VM_GET_COUNT:
		ret.user_ret = secondary_vm_count;
		break;

	case HF_VCPU_GET_COUNT:
		if (arg1 >= secondary_vm_count)
			ret.user_ret = -1;
		else
			ret.user_ret = secondary_vm[arg1].vcpu_count;
		break;

	case HF_VCPU_RUN:
		/* TODO: Make sure we don't allow secondary VMs to make this
		 * hvc call. */
		ret.user_ret = 1; /* WFI */
		if (arg1 < secondary_vm_count &&
		    arg2 < secondary_vm[arg1].vcpu_count &&
		    secondary_vm[arg1].vcpus[arg2].is_on) {
			arch_set_vm_mm(&secondary_vm[arg1].page_table);
			/* TODO: Update the virtual memory. */
			ret.new = secondary_vm[arg1].vcpus + arg2;
			ret.user_ret = 0;
		}
		break;

	default:
		ret.user_ret = -1;
	}

	return ret;
}

struct vcpu *irq_lower(void)
{
	/* TODO: Only switch if we know the interrupt was not for the secondary
	 * VM. */

	/* Switch back to primary VM, interrupts will be handled there. */
	arch_set_vm_mm(&primary_vm.page_table);
	return &primary_vm.vcpus[cpus - cpu()];
}

struct vcpu *sync_lower_exception(uint64_t esr)
{
	struct cpu *c = cpu();
	struct vcpu *vcpu = c->current;

	switch (esr >> 26) {
	case 0x01: /* EC = 000001, WFI or WFE. */
		/* Check TI bit of ISS, 0 = WFI, 1 = WFE. */
		if (esr & 1)
			return NULL;

		/* Switch back to primary VM. */
		arch_set_vm_mm(&primary_vm.page_table);
		vcpu = &primary_vm.vcpus[cpus - cpu()];

		dlog("Returning due to WFI\n");

		/* TODO: Use constant. */
		/* Set return value to 1, indicating to primary VM that this
		 * vcpu blocked on a WFI. */
		arch_regs_set_retval(&vcpu->regs, 1);
		return vcpu;

	case 0x24: /* EC = 100100, Data abort. */
		dlog("Data abort: pc=0x%x, esr=0x%x, ec=0x%x", vcpu->regs.pc, esr, esr >> 26);
		if (!(esr & (1u << 10))) /* Check FnV bit. */
			dlog(", far=0x%x, hpfar=0x%x", read_msr(far_el2), read_msr(hpfar_el2) << 8);
		else
			dlog(", far=invalid");

		dlog("\n");
		for (;;);

	default:
		dlog("Unknown sync exception pc=0x%x, esr=0x%x, ec=0x%x\n", vcpu->regs.pc, esr, esr >> 26);
		for (;;);
	}

	return NULL;
}
