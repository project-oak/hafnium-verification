#include "cpu.h"
#include "dlog.h"
#include "irq.h"
#include "vm.h"

#include "msr.h"

struct hvc_handler_return {
	size_t user_ret;
	bool schedule;
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

struct hvc_handler_return hvc_handler(size_t arg1)
{
	struct hvc_handler_return ret;

	ret.schedule = true;

	switch (arg1) {
	case 0x84000000: /* PSCI_VERSION */
		ret.user_ret = 2;
		break;

	case 0x84000006: /* PSCI_MIGRATE */
		ret.user_ret = 2;
		break;

#if 0
	TODO: Remove this.
	case 1: /* TODO: Fix. */
		{
			extern struct vm vm0;
			struct vcpu *vcpu = vm0.vcpus;
			vcpu->interrupt = true;
			vcpu_ready(vcpu);
			dlog("Readying VCPU0 again\n");
		}
		ret.user_ret = 0;
		break;
#endif

	default:
		ret.user_ret = -1;
	}

	return ret;
}

bool sync_lower_exception(uint64_t esr)
{
	struct cpu *c = cpu();
	struct vcpu *vcpu = c->current;

	switch (esr >> 26) {
	case 0x01: /* EC = 000001, WFI or WFE. */
		/* Check TI bit of ISS. */
		if (esr & 1)
			return true;
		//vcpu_unready(vcpu);
		return true;

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

	/* TODO: For now we always reschedule. But we shoudln't. */
	return true;
}
