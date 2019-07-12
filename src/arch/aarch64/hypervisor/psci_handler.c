/*
 * Copyright 2019 The Hafnium Authors.
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

#include "psci_handler.h"

#include <stdint.h>

#include "hf/arch/types.h"

#include "hf/api.h"
#include "hf/cpu.h"
#include "hf/dlog.h"
#include "hf/panic.h"
#include "hf/spci.h"
#include "hf/vm.h"

#include "psci.h"
#include "smc.h"

static uint32_t el3_psci_version;

void cpu_entry(struct cpu *c);

/* Performs arch specific boot time initialisation. */
void arch_one_time_init(void)
{
	el3_psci_version = smc32(PSCI_VERSION, 0, 0, 0);

	/* Check there's nothing unexpected about PSCI. */
	switch (el3_psci_version) {
	case PSCI_VERSION_0_2:
	case PSCI_VERSION_1_0:
	case PSCI_VERSION_1_1:
		/* Supported EL3 PSCI version. */
		dlog("Found PSCI version: %#x\n", el3_psci_version);
		break;

	default:
		/* Unsupported EL3 PSCI version. Log a warning but continue. */
		dlog("Warning: unknown PSCI version: %#x\n", el3_psci_version);
		el3_psci_version = 0;
		break;
	}
}

/**
 * Handles PSCI requests received via HVC or SMC instructions from the primary
 * VM.
 *
 * A minimal PSCI 1.1 interface is offered which can make use of the
 * implementation of PSCI in EL3 by acting as an adapter.
 *
 * Returns true if the request was a PSCI one, false otherwise.
 */
bool psci_primary_vm_handler(struct vcpu *vcpu, uint32_t func, uintreg_t arg0,
			     uintreg_t arg1, uintreg_t arg2, uintreg_t *ret)
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
		*ret = SMCCC_ERROR_UNKNOWN;
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
				*ret = smc32(func, arg0, 0, 0) & 0x3;
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
			*ret = PSCI_ERROR_NOT_SUPPORTED;
			break;
		}
		break;

	case PSCI_SYSTEM_OFF:
		smc32(PSCI_SYSTEM_OFF, 0, 0, 0);
		panic("System off failed");
		break;

	case PSCI_SYSTEM_RESET:
		smc32(PSCI_SYSTEM_RESET, 0, 0, 0);
		panic("System reset failed");
		break;

	case PSCI_AFFINITY_INFO:
		c = cpu_find(arg0);
		if (!c) {
			*ret = PSCI_ERROR_INVALID_PARAMETERS;
			break;
		}

		if (arg1 != 0) {
			*ret = PSCI_ERROR_NOT_SUPPORTED;
			break;
		}

		sl_lock(&c->lock);
		if (c->is_on) {
			*ret = PSCI_RETURN_ON;
		} else {
			*ret = PSCI_RETURN_OFF;
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
		arch_regs_set_pc_arg(vcpu_get_regs(vcpu), ipa_init(arg1), arg2);
		*ret = smc64(PSCI_CPU_SUSPEND, arg0, (uintreg_t)&cpu_entry,
			     (uintreg_t)vcpu_get_cpu(vcpu));
		break;
	}

	case PSCI_CPU_OFF:
		cpu_off(vcpu_get_cpu(vcpu));
		smc32(PSCI_CPU_OFF, 0, 0, 0);
		panic("CPU off failed");
		break;

	case PSCI_CPU_ON:
		c = cpu_find(arg0);
		if (!c) {
			*ret = PSCI_ERROR_INVALID_PARAMETERS;
			break;
		}

		if (cpu_on(c, ipa_init(arg1), arg2)) {
			*ret = PSCI_ERROR_ALREADY_ON;
			break;
		}

		/*
		 * There's a race when turning a CPU on when it's in the
		 * process of turning off. We need to loop here while it is
		 * reported that the CPU is on (because it's about to turn
		 * itself off).
		 */
		do {
			*ret = smc64(PSCI_CPU_ON, arg0, (uintreg_t)&cpu_entry,
				     (uintreg_t)c);
		} while (*ret == PSCI_ERROR_ALREADY_ON);

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
		*ret = PSCI_ERROR_NOT_SUPPORTED;
		break;

	default:
		return false;
	}

	return true;
}

/**
 * Convert a PSCI CPU / affinity ID for a secondary VM to the corresponding vCPU
 * index.
 */
spci_vcpu_index_t vcpu_id_to_index(cpu_id_t vcpu_id)
{
	/* For now we use indices as IDs for the purposes of PSCI. */
	return vcpu_id;
}

/**
 * Handles PSCI requests received via HVC or SMC instructions from a secondary
 * VM.
 *
 * A minimal PSCI 1.1 interface is offered which can start and stop vCPUs in
 * collaboration with the scheduler in the primary VM.
 *
 * Returns true if the request was a PSCI one, false otherwise.
 */
bool psci_secondary_vm_handler(struct vcpu *vcpu, uint32_t func, uintreg_t arg0,
			       uintreg_t arg1, uintreg_t arg2, uintreg_t *ret,
			       struct vcpu **next)
{
	switch (func & ~SMCCC_CONVENTION_MASK) {
	case PSCI_VERSION:
		*ret = PSCI_VERSION_1_1;
		break;

	case PSCI_FEATURES:
		switch (arg0 & ~SMCCC_CONVENTION_MASK) {
		case PSCI_CPU_SUSPEND:
			/*
			 * Does not offer OS-initiated mode but does use
			 * extended StateID Format.
			 */
			*ret = 0x2;
			break;

		case PSCI_VERSION:
		case PSCI_FEATURES:
		case PSCI_AFFINITY_INFO:
		case PSCI_CPU_OFF:
		case PSCI_CPU_ON:
			/* These are supported without special features. */
			*ret = 0;
			break;

		default:
			/* Everything else is unsupported. */
			*ret = PSCI_ERROR_NOT_SUPPORTED;
			break;
		}
		break;

	case PSCI_AFFINITY_INFO: {
		cpu_id_t target_affinity = arg0;
		uint32_t lowest_affinity_level = arg1;
		struct vm *vm = vcpu_get_vm(vcpu);
		struct vcpu *target_vcpu;
		struct vcpu_execution_locked vcpu_locked;
		spci_vcpu_index_t target_vcpu_index =
			vcpu_id_to_index(target_affinity);

		if (lowest_affinity_level != 0) {
			/* Affinity levels greater than 0 not supported. */
			*ret = PSCI_ERROR_INVALID_PARAMETERS;
			break;
		}

		if (target_vcpu_index >= vm_get_vcpu_count(vm)) {
			*ret = PSCI_ERROR_INVALID_PARAMETERS;
			break;
		}

		target_vcpu = vm_get_vcpu(vm, target_vcpu_index);
		if (!vcpu_try_lock(target_vcpu, &vcpu_locked)) {
			*ret = PSCI_RETURN_ON;
		} else {
			*ret = vcpu_is_off(vcpu_locked) ? PSCI_RETURN_OFF
							: PSCI_RETURN_ON;
			vcpu_unlock(&vcpu_locked);
		}
		break;
	}

	case PSCI_CPU_SUSPEND: {
		/*
		 * Downgrade suspend request to WFI and return SUCCESS, as
		 * allowed by the specification.
		 */
		*next = api_wait_for_interrupt(vcpu);
		*ret = PSCI_RETURN_SUCCESS;
		break;
	}

	case PSCI_CPU_OFF:
		/*
		 * Should never return to the caller, but in case it somehow
		 * does.
		 */
		*ret = PSCI_ERROR_DENIED;
		/* Tell the scheduler not to run the vCPU again. */
		*next = api_vcpu_off(vcpu);
		break;

	case PSCI_CPU_ON: {
		/* Parameter names as per PSCI specification. */
		cpu_id_t target_cpu = arg0;
		ipaddr_t entry_point_address = ipa_init(arg1);
		uint64_t context_id = arg2;
		spci_vcpu_index_t target_vcpu_index =
			vcpu_id_to_index(target_cpu);
		struct vm *vm = vcpu_get_vm(vcpu);
		struct vcpu *target_vcpu;

		if (target_vcpu_index >= vm_get_vcpu_count(vm)) {
			*ret = PSCI_ERROR_INVALID_PARAMETERS;
			break;
		}

		target_vcpu = vm_get_vcpu(vm, target_vcpu_index);

		if (vcpu_secondary_reset_and_start(
			    target_vcpu, entry_point_address, context_id)) {
			/*
			 * Tell the scheduler that it can start running the new
			 * vCPU now.
			 */
			*next = api_wake_up(vcpu, target_vcpu);
			*ret = PSCI_RETURN_SUCCESS;
		} else {
			*ret = PSCI_ERROR_ALREADY_ON;
		}

		break;
	}

	case PSCI_SYSTEM_OFF:
	case PSCI_SYSTEM_RESET:
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
		*ret = PSCI_ERROR_NOT_SUPPORTED;
		break;

	default:
		return false;
	}

	return true;
}

/**
 * Handles PSCI requests received via HVC or SMC instructions from a VM.
 * Requests from primary and secondary VMs are dealt with differently.
 *
 * Returns true if the request was a PSCI one, false otherwise.
 */
bool psci_handler(struct vcpu *vcpu, uint32_t func, uintreg_t arg0,
		  uintreg_t arg1, uintreg_t arg2, uintreg_t *ret,
		  struct vcpu **next)
{
	if (vm_get_id(vcpu_get_vm(vcpu)) == HF_PRIMARY_VM_ID) {
		return psci_primary_vm_handler(vcpu, func, arg0, arg1, arg2,
					       ret);
	}
	return psci_secondary_vm_handler(vcpu, func, arg0, arg1, arg2, ret,
					 next);
}
