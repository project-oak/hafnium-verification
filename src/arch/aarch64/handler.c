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

struct hvc_handler_return {
	uint64_t user_ret;
	struct vcpu *new;
};

int32_t smc(size_t arg0, size_t arg1, size_t arg2, size_t arg3);
void cpu_entry(struct cpu *c);

static struct vcpu *current(void)
{
	return (struct vcpu *)read_msr(tpidr_el2);
}

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

/**
 * Handles PSCI requests received via HVC or SMC instructions from the primary
 * VM only.
 *
 * Returns true if the request was a PSCI one, false otherwise.
 */
static bool psci_handler(uint32_t func, size_t arg0, size_t arg1, size_t arg2,
			 int32_t *ret)
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
			sret = smc(PSCI_CPU_ON, arg0, (size_t)&cpu_entry,
				   (size_t)c);
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

struct hvc_handler_return hvc_handler(size_t arg0, size_t arg1, size_t arg2,
				      size_t arg3)
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

	case HF_VM_CONFIGURE:
		ret.user_ret = api_vm_configure(ipa_init(arg1), ipa_init(arg2),
						current());
		break;

	case HF_MAILBOX_SEND:
		ret.user_ret =
			api_mailbox_send(arg1, arg2, current(), &ret.new);
		break;

	case HF_MAILBOX_RECEIVE:
		ret.user_ret = hf_mailbox_receive_return_encode(
			api_mailbox_receive(arg1, current(), &ret.new));
		break;

	case HF_MAILBOX_CLEAR:
		ret.user_ret = api_mailbox_clear(current());
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
	return api_yield(current());
}

struct vcpu *sync_lower_exception(uint64_t esr)
{
	struct vcpu *vcpu = current();
	int32_t ret;

	switch (esr >> 26) {
	case 0x01: /* EC = 000001, WFI or WFE. */
		/* Check TI bit of ISS, 0 = WFI, 1 = WFE. */
		if (esr & 1) {
			return NULL;
		}
		return api_wait_for_interrupt(current());

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

	case 0x17: /* EC = 010111, SMC instruction. */
		if (vcpu->vm->id != HF_PRIMARY_VM_ID ||
		    !psci_handler(vcpu->regs.r[0], vcpu->regs.r[1],
				  vcpu->regs.r[2], vcpu->regs.r[3], &ret)) {
			dlog("Unsupported SMC call: 0x%x\n", vcpu->regs.r[0]);
			ret = -1;
		}

		/* Skip the SMC instruction. */
		vcpu->regs.pc += (esr & (1u << 25)) ? 4 : 2;
		break;

	default:
		dlog("Unknown lower sync exception pc=0x%x, esr=0x%x, "
		     "ec=0x%x\n",
		     vcpu->regs.pc, esr, esr >> 26);
		for (;;) {
			/* do nothing */
		}
	}

	vcpu->regs.r[0] = ret;

	return NULL;
}
