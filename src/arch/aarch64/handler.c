/*
 * Copyright 2018 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "hf/api.h"
#include "hf/cpu.h"
#include "hf/dlog.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

#include "msr.h"
#include "psci.h"
#include "smc.h"

#define HCR_EL2_VI (1u << 7)

struct hvc_handler_return {
	uintreg_t user_ret;
	struct vcpu *new;
};

void cpu_entry(struct cpu *c);

static inline struct vcpu *current(void)
{
	return (struct vcpu *)read_msr(tpidr_el2);
}

/**
 * Saves the state of per-vCPU peripherals, such as the virtual timer, and
 * informs the arch-independent sections that registers have been saved.
 */
void complete_saving_state(struct vcpu *vcpu)
{
	vcpu->regs.lazy.cntv_cval_el0 = read_msr(cntv_cval_el0);
	vcpu->regs.lazy.cntv_ctl_el0 = read_msr(cntv_ctl_el0);

	api_regs_state_saved(vcpu);

	/*
	 * If switching away from the primary, copy the current EL0 virtual
	 * timer registers to the corresponding EL2 physical timer registers.
	 * This is used to emulate the virtual timer for the primary in case it
	 * should fire while the secondary is running.
	 */
	if (vcpu->vm->id == HF_PRIMARY_VM_ID) {
		/*
		 * Clear timer control register before copying compare value, to
		 * avoid a spurious timer interrupt. This could be a problem if
		 * the interrupt is configured as edge-triggered, as it would
		 * then be latched in.
		 */
		write_msr(cnthp_ctl_el2, 0);
		write_msr(cnthp_cval_el2, read_msr(cntv_cval_el0));
		write_msr(cnthp_ctl_el2, read_msr(cntv_ctl_el0));
	}
}

/**
 * Restores the state of per-vCPU peripherals, such as the virtual timer.
 */
void begin_restoring_state(struct vcpu *vcpu)
{
	/*
	 * Clear timer control register before restoring compare value, to avoid
	 * a spurious timer interrupt. This could be a problem if the interrupt
	 * is configured as edge-triggered, as it would then be latched in.
	 */
	write_msr(cntv_ctl_el0, 0);
	write_msr(cntv_cval_el0, vcpu->regs.lazy.cntv_cval_el0);
	write_msr(cntv_ctl_el0, vcpu->regs.lazy.cntv_ctl_el0);

	/*
	 * If we are switching (back) to the primary, disable the EL2 physical
	 * timer which was being used to emulate the EL0 virtual timer, as the
	 * virtual timer is now running for the primary again.
	 */
	if (vcpu->vm->id == HF_PRIMARY_VM_ID) {
		write_msr(cnthp_ctl_el2, 0);
		write_msr(cnthp_cval_el2, 0);
	}
}

void irq_current_exception(uintreg_t elr, uintreg_t spsr)
{
	(void)elr;
	(void)spsr;

	dlog("IRQ from current\n");
	for (;;) {
		/* do nothing */
	}
}

void fiq_current_exception(uintreg_t elr, uintreg_t spsr)
{
	(void)elr;
	(void)spsr;

	dlog("FIQ from current\n");
	for (;;) {
		/* do nothing */
	}
}

void serr_current_exception(uintreg_t elr, uintreg_t spsr)
{
	(void)elr;
	(void)spsr;

	dlog("SERR from current\n");
	for (;;) {
		/* do nothing */
	}
}

void sync_current_exception(uintreg_t elr, uintreg_t spsr)
{
	uintreg_t esr = read_msr(esr_el2);

	(void)spsr;

	switch (esr >> 26) {
	case 0x25: /* EC = 100101, Data abort. */
		dlog("Data abort: pc=0x%x, esr=0x%x, ec=0x%x", elr, esr,
		     esr >> 26);
		if (!(esr & (1u << 10))) { /* Check FnV bit. */
			dlog(", far=0x%x", read_msr(far_el2));
		} else {
			dlog(", far=invalid");
		}

		dlog("\n");
		break;

	default:
		dlog("Unknown current sync exception pc=0x%x, esr=0x%x, "
		     "ec=0x%x\n",
		     elr, esr, esr >> 26);
	}

	for (;;) {
		/* do nothing */
	}
}

/**
 * Handles PSCI requests received via HVC or SMC instructions from the primary
 * VM only.
 *
 * Returns true if the request was a PSCI one, false otherwise.
 */
static bool psci_handler(uint32_t func, uintreg_t arg0, uintreg_t arg1,
			 uintreg_t arg2, int32_t *ret)
{
	struct cpu *c;
	int32_t sret;

	switch (func & ~PSCI_CONVENTION_MASK) {
	case PSCI_VERSION:
		/* Version is 0.2. */
		*ret = 2;
		break;

	case PSCI_MIGRATE_INFO_TYPE:
		/* Trusted OS does not require migration. */
		*ret = 2;
		break;

	case PSCI_SYSTEM_OFF:
		smc(PSCI_SYSTEM_OFF, 0, 0, 0);
		for (;;) {
		}
		break;

	case PSCI_SYSTEM_RESET:
		smc(PSCI_SYSTEM_RESET, 0, 0, 0);
		for (;;) {
		}
		break;

	case PSCI_AFFINITY_INFO:
		c = cpu_find(arg0);
		if (!c) {
			*ret = PSCI_RETURN_INVALID_PARAMETERS;
			break;
		}

		if (arg1 != 0) {
			*ret = PSCI_RETURN_NOT_SUPPORTED;
			break;
		}

		sl_lock(&c->lock);
		if (c->is_on) {
			*ret = 0; /* ON */
		} else {
			*ret = 1; /* OFF */
		}
		sl_unlock(&c->lock);
		break;

	case PSCI_CPU_OFF:
		cpu_off(current()->cpu);
		smc(PSCI_CPU_OFF, 0, 0, 0);
		for (;;) {
		}
		break;

	case PSCI_CPU_ON:
		c = cpu_find(arg0);
		if (!c) {
			*ret = PSCI_RETURN_INVALID_PARAMETERS;
			break;
		}

		if (cpu_on(c, ipa_init(arg1), arg2)) {
			*ret = PSCI_RETURN_ALREADY_ON;
			break;
		}

		/*
		 * There's a race when turning a CPU on when it's in the
		 * process of turning off. We need to loop here while it is
		 * reported that the CPU is on (because it's about to turn
		 * itself off).
		 */
		do {
			sret = smc(PSCI_CPU_ON, arg0, (uintreg_t)&cpu_entry,
				   (uintreg_t)c);
		} while (sret == PSCI_RETURN_ALREADY_ON);

		if (sret == PSCI_RETURN_SUCCESS) {
			*ret = PSCI_RETURN_SUCCESS;
		} else {
			dlog("Unexpected return from PSCI_CPU_ON: 0x%x\n",
			     sret);
			*ret = PSCI_RETURN_INTERNAL_FAILURE;
		}
		break;

	default:
		return false;
	}

	return true;
}

/**
 * Sets or clears the VI bit in the HCR_EL2 register saved in the given
 * arch_regs.
 */
static void set_virtual_interrupt(struct arch_regs *r, bool enable)
{
	if (enable) {
		r->lazy.hcr_el2 |= HCR_EL2_VI;
	} else {
		r->lazy.hcr_el2 &= ~HCR_EL2_VI;
	}
}

/**
 * Sets or clears the VI bit in the HCR_EL2 register.
 */
static void set_virtual_interrupt_current(bool enable)
{
	uintreg_t hcr_el2 = read_msr(hcr_el2);

	if (enable) {
		hcr_el2 |= HCR_EL2_VI;
	} else {
		hcr_el2 &= ~HCR_EL2_VI;
	}
	write_msr(hcr_el2, hcr_el2);
}

struct hvc_handler_return hvc_handler(uintreg_t arg0, uintreg_t arg1,
				      uintreg_t arg2, uintreg_t arg3)
{
	struct hvc_handler_return ret;

	ret.new = NULL;

	if (current()->vm->id == HF_PRIMARY_VM_ID) {
		int32_t psci_ret;

		if (psci_handler(arg0, arg1, arg2, arg3, &psci_ret)) {
			ret.user_ret = psci_ret;
			return ret;
		}
	}

	switch ((uint32_t)arg0 & ~PSCI_CONVENTION_MASK) {
	case HF_VM_GET_ID:
		ret.user_ret = api_vm_get_id(current());
		break;

	case HF_VM_GET_COUNT:
		ret.user_ret = api_vm_get_count();
		break;

	case HF_VCPU_GET_COUNT:
		ret.user_ret = api_vcpu_get_count(arg1, current());
		break;

	case HF_VCPU_RUN:
		ret.user_ret = hf_vcpu_run_return_encode(
			api_vcpu_run(arg1, arg2, current(), &ret.new));
		break;

	case HF_VCPU_YIELD:
		ret.user_ret = 0;
		ret.new = api_yield(current());
		break;

	case HF_VM_CONFIGURE:
		ret.user_ret = api_vm_configure(ipa_init(arg1), ipa_init(arg2),
						current(), &ret.new);
		break;

	case HF_MAILBOX_SEND:
		ret.user_ret =
			api_mailbox_send(arg1, arg2, arg3, current(), &ret.new);
		break;

	case HF_MAILBOX_RECEIVE:
		ret.user_ret = hf_mailbox_receive_return_encode(
			api_mailbox_receive(arg1, current(), &ret.new));
		break;

	case HF_MAILBOX_CLEAR:
		ret.user_ret = api_mailbox_clear(current(), &ret.new);
		break;

	case HF_MAILBOX_WRITABLE_GET:
		ret.user_ret = api_mailbox_writable_get(current());
		break;

	case HF_MAILBOX_WAITER_GET:
		ret.user_ret = api_mailbox_waiter_get(arg1, current());
		break;

	case HF_INTERRUPT_ENABLE:
		ret.user_ret = api_interrupt_enable(arg1, arg2, current());
		break;

	case HF_INTERRUPT_GET:
		ret.user_ret = api_interrupt_get(current());
		break;

	case HF_INTERRUPT_INJECT:
		ret.user_ret = api_interrupt_inject(arg1, arg2, arg3, current(),
						    &ret.new);
		break;

	case HF_SHARE_MEMORY:
		ret.user_ret =
			api_share_memory(arg1 >> 32, ipa_init(arg2), arg3,
					 arg1 & 0xffffffff, current());
		break;

	default:
		ret.user_ret = -1;
	}

	/* Set or clear VI bit. */
	if (ret.new == NULL) {
		/*
		 * Not switching vCPUs, set the bit for the current vCPU
		 * directly in the register.
		 */
		set_virtual_interrupt_current(
			current()->interrupts.enabled_and_pending_count > 0);
	} else {
		/*
		 * About to switch vCPUs, set the bit for the vCPU to which we
		 * are switching in the saved copy of the register.
		 */
		set_virtual_interrupt(
			&ret.new->regs,
			ret.new->interrupts.enabled_and_pending_count > 0);
	}

	return ret;
}

struct vcpu *irq_lower(void)
{
	/*
	 * Switch back to primary VM, interrupts will be handled there.
	 *
	 * If the VM has aborted, this vCPU will be aborted when the scheduler
	 * tries to run it again. This means the interrupt will not be delayed
	 * by the aborted VM.
	 *
	 * TODO: Only switch when the interrupt isn't for the current VM.
	 */
	return api_preempt(current());
}

struct vcpu *fiq_lower(void)
{
	return irq_lower();
}

struct vcpu *serr_lower(void)
{
	dlog("SERR from lower\n");
	return api_abort(current());
}

struct vcpu *sync_lower_exception(uintreg_t esr)
{
	struct vcpu *vcpu = current();
	int32_t ret;

	switch (esr >> 26) {
	case 0x01: /* EC = 000001, WFI or WFE. */
		/* Check TI bit of ISS, 0 = WFI, 1 = WFE. */
		if (esr & 1) {
			return NULL;
		}
		/* Skip the WFI instruction. */
		vcpu->regs.pc += (esr & (1u << 25)) ? 4 : 2;
		return api_wait_for_interrupt(vcpu);

	case 0x24: /* EC = 100100, Data abort. */
		dlog("Lower data abort: pc=0x%x, esr=0x%x, ec=0x%x, vmid=%u, "
		     "vcpu=%u",
		     vcpu->regs.pc, esr, esr >> 26, vcpu->vm->id,
		     vcpu_index(vcpu));
		if (!(esr & (1u << 10))) { /* Check FnV bit. */
			dlog(", far=0x%x, hpfar=0x%x", read_msr(far_el2),
			     read_msr(hpfar_el2) << 8);
		} else {
			dlog(", far=invalid");
		}

		dlog("\n");
		break;

	case 0x20: /* EC = 100000, Instruction abort. */
		dlog("Lower instruction abort: pc=0x%x, esr=0x%x, ec=0x%x, "
		     "vmdid=%u, vcpu=%u",
		     vcpu->regs.pc, esr, esr >> 26, vcpu->vm->id,
		     vcpu_index(vcpu));
		if (!(esr & (1u << 10))) { /* Check FnV bit. */
			dlog(", far=0x%x, hpfar=0x%x", read_msr(far_el2),
			     read_msr(hpfar_el2) << 8);
		} else {
			dlog(", far=invalid");
		}

		dlog(", vttbr_el2=0x%x", read_msr(vttbr_el2));
		dlog("\n");
		break;

	case 0x17: /* EC = 010111, SMC instruction. */
		if (vcpu->vm->id != HF_PRIMARY_VM_ID ||
		    !psci_handler(vcpu->regs.r[0], vcpu->regs.r[1],
				  vcpu->regs.r[2], vcpu->regs.r[3], &ret)) {
			dlog("Unsupported SMC call: 0x%x\n", vcpu->regs.r[0]);
			ret = -1;
		}

		/* Skip the SMC instruction. */
		vcpu->regs.pc += (esr & (1u << 25)) ? 4 : 2;
		vcpu->regs.r[0] = ret;
		return NULL;

	default:
		dlog("Unknown lower sync exception pc=0x%x, esr=0x%x, "
		     "ec=0x%x\n",
		     vcpu->regs.pc, esr, esr >> 26);
		break;
	}

	/* The exception wasn't handled so abort the VM. */
	return api_abort(vcpu);
}
