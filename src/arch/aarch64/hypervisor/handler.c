/*
 * Copyright 2018 The Hafnium Authors.
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

#include <stdnoreturn.h>

#include "hf/arch/barriers.h"
#include "hf/arch/init.h"

#include "hf/api.h"
#include "hf/cpu.h"
#include "hf/dlog.h"
#include "hf/panic.h"
#include "hf/spci.h"
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

static uint32_t el3_psci_version = 0;

/* Performs arch specific boot time initialisation. */
void arch_one_time_init(void)
{
	el3_psci_version = smc(PSCI_VERSION, 0, 0, 0);

	/* Check there's nothing unexpected about PSCI. */
	switch (el3_psci_version) {
	case PSCI_VERSION_0_2:
	case PSCI_VERSION_1_0:
	case PSCI_VERSION_1_1:
		/* Supported EL3 PSCI version. */
		dlog("Found PSCI version: 0x%x\n", el3_psci_version);
		break;

	default:
		/* Unsupported EL3 PSCI version. Log a warning but continue. */
		dlog("Warning: unknown PSCI version: 0x%x\n", el3_psci_version);
		el3_psci_version = 0;
		break;
	}
}

/* Gets a reference to the currently executing vCPU. */
static struct vcpu *current(void)
{
	return (struct vcpu *)read_msr(tpidr_el2);
}

/**
 * Saves the state of per-vCPU peripherals, such as the virtual timer, and
 * informs the arch-independent sections that registers have been saved.
 */
void complete_saving_state(struct vcpu *vcpu)
{
	vcpu->regs.peripherals.cntv_cval_el0 = read_msr(cntv_cval_el0);
	vcpu->regs.peripherals.cntv_ctl_el0 = read_msr(cntv_ctl_el0);

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
	write_msr(cntv_cval_el0, vcpu->regs.peripherals.cntv_cval_el0);
	write_msr(cntv_ctl_el0, vcpu->regs.peripherals.cntv_ctl_el0);

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

/**
 * Ensures all explicit memory access and management instructions for
 * non-shareable normal memory have completed before continuing.
 */
static void dsb_nsh(void)
{
	__asm__ volatile("dsb nsh");
}

/**
 * Invalidate all stage 1 TLB entries on the current (physical) CPU for the
 * current VMID.
 */
static void invalidate_vm_tlb(void)
{
	isb();
	__asm__ volatile("tlbi vmalle1");
	isb();
	dsb_nsh();
}

/**
 * Invalidates the TLB if a different vCPU is being run than the last vCPU of
 * the same VM which was run on the current pCPU.
 *
 * This is necessary because VMs may (contrary to the architecture
 * specification) use inconsistent ASIDs across vCPUs. c.f. KVM's similar
 * workaround:
 * https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/commit/?id=94d0e5980d6791b9
 */
void maybe_invalidate_tlb(struct vcpu *vcpu)
{
	size_t current_cpu_index = cpu_index(vcpu->cpu);
	size_t new_vcpu_index = vcpu_index(vcpu);

	if (vcpu->vm->arch.last_vcpu_on_cpu[current_cpu_index] !=
	    new_vcpu_index) {
		/*
		 * The vCPU has changed since the last time this VM was run on
		 * this pCPU, so we need to invalidate the TLB.
		 */
		invalidate_vm_tlb();

		/* Record the fact that this vCPU is now running on this CPU. */
		vcpu->vm->arch.last_vcpu_on_cpu[current_cpu_index] =
			new_vcpu_index;
	}
}

noreturn void irq_current_exception(uintreg_t elr, uintreg_t spsr)
{
	(void)elr;
	(void)spsr;

	panic("IRQ from current");
}

noreturn void fiq_current_exception(uintreg_t elr, uintreg_t spsr)
{
	(void)elr;
	(void)spsr;

	panic("FIQ from current");
}

noreturn void serr_current_exception(uintreg_t elr, uintreg_t spsr)
{
	(void)elr;
	(void)spsr;

	panic("SERR from current");
}

noreturn void sync_current_exception(uintreg_t elr, uintreg_t spsr)
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
		break;
	}

	panic("EL2 exception");
}

/**
 * Handles PSCI requests received via HVC or SMC instructions from the primary
 * VM only.
 *
 * A minimal PSCI 1.1 interface is offered which can make use of previous
 * version of PSCI in EL3 by acting as an adapter.
 *
 * Returns true if the request was a PSCI one, false otherwise.
 */
static bool psci_handler(uint32_t func, uintreg_t arg0, uintreg_t arg1,
			 uintreg_t arg2, int32_t *ret)
{
	struct cpu *c;

	/*
	 * If there's a problem with the EL3 PSCI, block standard secure service
	 * calls by marking them as unknown. Other calls will be allowed to pass
	 * through.
	 *
	 * This blocks more calls than just PSCI so it may need to be made more
	 * lenient in future.
	 */
	if (el3_psci_version == 0) {
		*ret = SMCCC_RETURN_UNKNOWN;
		return (func & SMCCC_SERVICE_CALL_MASK) ==
		       SMCCC_STANDARD_SECURE_SERVICE_CALL;
	}

	switch (func & ~SMCCC_CONVENTION_MASK) {
	case PSCI_VERSION:
		*ret = PSCI_VERSION_1_1;
		break;

	case PSCI_FEATURES:
		switch (arg0 & ~SMCCC_CONVENTION_MASK) {
		case PSCI_CPU_SUSPEND:
			if (el3_psci_version == PSCI_VERSION_0_2) {
				/*
				 * PSCI 0.2 doesn't support PSCI_FEATURES so
				 * report PSCI 0.2 compatible features.
				 */
				*ret = 0;
			} else {
				/* PSCI 1.x only defines two feature bits. */
				*ret = smc(func, arg0, 0, 0) & 0x3;
			}
			break;

		case PSCI_VERSION:
		case PSCI_FEATURES:
		case PSCI_SYSTEM_OFF:
		case PSCI_SYSTEM_RESET:
		case PSCI_AFFINITY_INFO:
		case PSCI_CPU_OFF:
		case PSCI_CPU_ON:
			/* These are supported without special features. */
			*ret = 0;
			break;

		default:
			/* Everything else is unsupported. */
			*ret = PSCI_RETURN_NOT_SUPPORTED;
			break;
		}
		break;

	case PSCI_SYSTEM_OFF:
		smc(PSCI_SYSTEM_OFF, 0, 0, 0);
		panic("System off failed");
		break;

	case PSCI_SYSTEM_RESET:
		smc(PSCI_SYSTEM_RESET, 0, 0, 0);
		panic("System reset failed");
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

	case PSCI_CPU_SUSPEND: {
		/*
		 * Update vcpu state to wake from the provided entry point but
		 * if suspend returns, for example because it failed or was a
		 * standby power state, the SMC will return and the updated
		 * vcpu registers will be ignored.
		 */
		struct vcpu *vcpu = current();

		arch_regs_set_pc_arg(&vcpu->regs, ipa_init(arg1), arg2);
		*ret = smc(PSCI_CPU_SUSPEND | SMCCC_64_BIT, arg0,
			   (uintreg_t)&cpu_entry, (uintreg_t)vcpu->cpu);
		break;
	}

	case PSCI_CPU_OFF:
		cpu_off(current()->cpu);
		smc(PSCI_CPU_OFF, 0, 0, 0);
		panic("CPU off failed");
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
			*ret = smc(PSCI_CPU_ON | SMCCC_64_BIT, arg0,
				   (uintreg_t)&cpu_entry, (uintreg_t)c);
		} while (*ret == PSCI_RETURN_ALREADY_ON);

		if (*ret != PSCI_RETURN_SUCCESS) {
			cpu_off(c);
		}
		break;

	case PSCI_MIGRATE:
	case PSCI_MIGRATE_INFO_TYPE:
	case PSCI_MIGRATE_INFO_UP_CPU:
	case PSCI_CPU_FREEZE:
	case PSCI_CPU_DEFAULT_SUSPEND:
	case PSCI_NODE_HW_STATE:
	case PSCI_SYSTEM_SUSPEND:
	case PSCI_SET_SYSPEND_MODE:
	case PSCI_STAT_RESIDENCY:
	case PSCI_STAT_COUNT:
	case PSCI_SYSTEM_RESET2:
	case PSCI_MEM_PROTECT:
	case PSCI_MEM_PROTECT_CHECK_RANGE:
		/* Block all other known PSCI calls. */
		*ret = PSCI_RETURN_NOT_SUPPORTED;
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

	switch ((uint32_t)arg0) {
	case SPCI_VERSION_32:
		ret.user_ret = api_spci_version();
		break;

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

	case SPCI_YIELD_32:
		ret.user_ret = api_spci_yield(current(), &ret.new);
		break;

	case HF_VM_CONFIGURE:
		ret.user_ret = api_vm_configure(ipa_init(arg1), ipa_init(arg2),
						current(), &ret.new);
		break;

	case SPCI_MSG_SEND_32:
		ret.user_ret = api_spci_msg_send(arg1, current(), &ret.new);
		break;

	case SPCI_MSG_RECV_32:
		ret.user_ret = api_spci_msg_recv(arg1, current(), &ret.new);
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

/**
 * Initialises a fault info structure. It assumes that an FnV bit exists at
 * bit offset 10 of the ESR, and that it is only valid when the bottom 6 bits of
 * the ESR (the fault status code) are 010000; this is the case for both
 * instruction and data aborts, but not necessarily for other exception reasons.
 */
static struct vcpu_fault_info fault_info_init(uintreg_t esr,
					      const struct vcpu *vcpu, int mode)
{
	uint32_t fsc = esr & 0x3f;
	struct vcpu_fault_info r;

	r.mode = mode;
	r.pc = va_init(vcpu->regs.pc);

	/*
	 * Check the FnV bit, which is only valid if dfsc/ifsc is 010000. It
	 * indicates that we cannot rely on far_el2.
	 */
	if (fsc == 0x10 && esr & (1u << 10)) {
		r.vaddr = va_init(0);
		r.ipaddr = ipa_init(read_msr(hpfar_el2) << 8);
	} else {
		r.vaddr = va_init(read_msr(far_el2));
		r.ipaddr = ipa_init((read_msr(hpfar_el2) << 8) |
				    (read_msr(far_el2) & (PAGE_SIZE - 1)));
	}

	return r;
}

struct vcpu *sync_lower_exception(uintreg_t esr)
{
	struct vcpu *vcpu = current();
	struct vcpu_fault_info info;
	struct vcpu *new_vcpu;

	switch (esr >> 26) {
	case 0x01: /* EC = 000001, WFI or WFE. */
		/* Skip the instruction. */
		vcpu->regs.pc += (esr & (1u << 25)) ? 4 : 2;
		/* Check TI bit of ISS, 0 = WFI, 1 = WFE. */
		if (esr & 1) {
			/* WFE */
			/*
			 * TODO: consider giving the scheduler more context,
			 * somehow.
			 */
			api_spci_yield(vcpu, &new_vcpu);
			return new_vcpu;
		}
		/* WFI */
		return api_wait_for_interrupt(vcpu);

	case 0x24: /* EC = 100100, Data abort. */
		info = fault_info_init(
			esr, vcpu, (esr & (1u << 6)) ? MM_MODE_W : MM_MODE_R);
		if (vcpu_handle_page_fault(vcpu, &info)) {
			return NULL;
		}
		break;

	case 0x20: /* EC = 100000, Instruction abort. */
		info = fault_info_init(esr, vcpu, MM_MODE_X);
		if (vcpu_handle_page_fault(vcpu, &info)) {
			return NULL;
		}
		break;

	case 0x17: /* EC = 010111, SMC instruction. */ {
		uintreg_t smc_pc = vcpu->regs.pc;
		int32_t ret;

		if (vcpu->vm->id != HF_PRIMARY_VM_ID ||
		    !psci_handler(vcpu->regs.r[0], vcpu->regs.r[1],
				  vcpu->regs.r[2], vcpu->regs.r[3], &ret)) {
			dlog("Unsupported SMC call: 0x%x\n", vcpu->regs.r[0]);
			ret = PSCI_RETURN_NOT_SUPPORTED;
		}

		/* Skip the SMC instruction. */
		vcpu->regs.pc = smc_pc + (esr & (1u << 25) ? 4 : 2);
		vcpu->regs.r[0] = ret;
		return NULL;
	}

	default:
		dlog("Unknown lower sync exception pc=0x%x, esr=0x%x, "
		     "ec=0x%x\n",
		     vcpu->regs.pc, esr, esr >> 26);
		break;
	}

	/* The exception wasn't handled so abort the VM. */
	return api_abort(vcpu);
}
