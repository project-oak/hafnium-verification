#include "api.h"
#include "arch_api.h"
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
	for (;;) {
		/* do nothing */
	}
}

void sync_current_exception(uint64_t esr, uint64_t elr)
{
	switch (esr >> 26) {
	case 0x25: /* EC = 100101, Data abort. */
		dlog("Data abort: pc=0x%x, esr=0x%x, ec=0x%x", elr, esr,
		     esr >> 26);
		if (!(esr & (1u << 10))) { /* Check FnV bit. */
			dlog(", far=0x%x, hpfar=0x%x", read_msr(far_el2),
			     read_msr(hpfar_el2) << 8);
		} else {
			dlog(", far=invalid");
		}

		dlog("\n");
		for (;;) {
			/* do nothing */
		}

	default:
		dlog("Unknown current sync exception pc=0x%x, esr=0x%x, "
		     "ec=0x%x\n",
		     elr, esr, esr >> 26);
		for (;;) {
			/* do nothing */
		}
	}
	for (;;) {
		/* do nothing */
	}
}

struct hvc_handler_return hvc_handler(size_t arg0, size_t arg1, size_t arg2,
				      size_t arg3)
{
	(void)arg3;

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
		ret.user_ret = api_vm_get_count();
		break;

	case HF_VCPU_GET_COUNT:
		ret.user_ret = api_vcpu_get_count(arg1);
		break;

	case HF_VCPU_RUN:
		ret.user_ret = api_vcpu_run(arg1, arg2, &ret.new);
		break;

	case HF_VM_CONFIGURE:
		ret.user_ret = api_vm_configure(arg1, arg2);
		break;

	case HF_RPC_REQUEST:
		ret.user_ret = api_rpc_request(arg1, arg2);
		break;

	case HF_RPC_READ_REQUEST:
		ret.user_ret = api_rpc_read_request(arg1, &ret.new);
		break;

	case HF_RPC_ACK:
		ret.user_ret = api_rpc_ack();
		break;

	case HF_RPC_REPLY:
		ret.user_ret = api_rpc_reply(arg1, arg2, &ret.new);
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
	return api_switch_to_primary(HF_VCPU_YIELD, vcpu_state_ready);
}

struct vcpu *sync_lower_exception(uint64_t esr)
{
	struct cpu *c = cpu();
	struct vcpu *vcpu = c->current;

	switch (esr >> 26) {
	case 0x01: /* EC = 000001, WFI or WFE. */
		/* Check TI bit of ISS, 0 = WFI, 1 = WFE. */
		if (esr & 1) {
			return NULL;
		}
		return api_wait_for_interrupt();

	case 0x24: /* EC = 100100, Data abort. */
		dlog("Data abort: pc=0x%x, esr=0x%x, ec=0x%x", vcpu->regs.pc,
		     esr, esr >> 26);
		if (!(esr & (1u << 10))) { /* Check FnV bit. */
			dlog(", far=0x%x, hpfar=0x%x", read_msr(far_el2),
			     read_msr(hpfar_el2) << 8);
		} else {
			dlog(", far=invalid");
		}

		dlog("\n");
		for (;;) {
			/* do nothing */
		}

	case 0x20: /* EC = 100000, Instruction abort. */
		dlog("Instruction abort: pc=0x%x, esr=0x%x, ec=0x%x",
		     vcpu->regs.pc, esr, esr >> 26);
		if (!(esr & (1u << 10))) { /* Check FnV bit. */
			dlog(", far=0x%x, hpfar=0x%x", read_msr(far_el2),
			     read_msr(hpfar_el2) << 8);
		} else {
			dlog(", far=invalid");
		}

		dlog(", vttbr_el2=0x%x", read_msr(vttbr_el2));
		dlog("\n");
		for (;;) {
			/* do nothing */
		}

	default:
		dlog("Unknown lower sync exception pc=0x%x, esr=0x%x, "
		     "ec=0x%x\n",
		     vcpu->regs.pc, esr, esr >> 26);
		for (;;) {
			/* do nothing */
		}
	}

	return NULL;
}
