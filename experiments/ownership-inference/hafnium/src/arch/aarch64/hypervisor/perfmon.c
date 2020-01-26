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

#include "perfmon.h"

#include "hf/check.h"
#include "hf/dlog.h"
#include "hf/types.h"

#include "msr.h"
#include "sysregs.h"

/* clang-format off */

/**
 * Definitions of read-only performance monitor registers' encodings.
 * See Arm Architecture Reference Manual Armv8-A, D12.3.1.
 * NAME, op0, op1, crn, crm, op2
 */
#define PERFMON_REGISTERS_READ                 \
	X(PMCEID0_EL0       , 3, 3,  9, 12, 6) \
	X(PMCEID1_EL0       , 3, 3,  9, 12, 7) \
	X(PMEVCNTR0_EL0     , 3, 3, 14,  8, 0) \
	X(PMEVCNTR1_EL0     , 3, 3, 14,  8, 1) \
	X(PMEVCNTR2_EL0     , 3, 3, 14,  8, 2) \
	X(PMEVCNTR3_EL0     , 3, 3, 14,  8, 3) \
	X(PMEVCNTR4_EL0     , 3, 3, 14,  8, 4) \
	X(PMEVCNTR5_EL0     , 3, 3, 14,  8, 5) \
	X(PMEVCNTR6_EL0     , 3, 3, 14,  8, 6) \
	X(PMEVCNTR7_EL0     , 3, 3, 14,  8, 7) \
	X(PMEVCNTR8_EL0     , 3, 3, 14,  9, 0) \
	X(PMEVCNTR9_EL0     , 3, 3, 14,  9, 1) \
	X(PMEVCNTR10_EL0    , 3, 3, 14,  9, 2) \
	X(PMEVCNTR11_EL0    , 3, 3, 14,  9, 3) \
	X(PMEVCNTR12_EL0    , 3, 3, 14,  9, 4) \
	X(PMEVCNTR13_EL0    , 3, 3, 14,  9, 5) \
	X(PMEVCNTR14_EL0    , 3, 3, 14,  9, 6) \
	X(PMEVCNTR15_EL0    , 3, 3, 14,  9, 7) \
	X(PMEVCNTR16_EL0    , 3, 3, 14, 10, 0) \
	X(PMEVCNTR17_EL0    , 3, 3, 14, 10, 1) \
	X(PMEVCNTR18_EL0    , 3, 3, 14, 10, 2) \
	X(PMEVCNTR19_EL0    , 3, 3, 14, 10, 3) \
	X(PMEVCNTR20_EL0    , 3, 3, 14, 10, 4) \
	X(PMEVCNTR21_EL0    , 3, 3, 14, 10, 5) \
	X(PMEVCNTR22_EL0    , 3, 3, 14, 10, 6) \
	X(PMEVCNTR23_EL0    , 3, 3, 14, 10, 7) \
	X(PMEVCNTR24_EL0    , 3, 3, 14, 11, 0) \
	X(PMEVCNTR25_EL0    , 3, 3, 14, 11, 1) \
	X(PMEVCNTR26_EL0    , 3, 3, 14, 11, 2) \
	X(PMEVCNTR27_EL0    , 3, 3, 14, 11, 3) \
	X(PMEVCNTR28_EL0    , 3, 3, 14, 11, 4) \
	X(PMEVCNTR29_EL0    , 3, 3, 14, 11, 5) \
	X(PMEVCNTR30_EL0    , 3, 3, 14, 11, 6) \

/**
 * Definitions of write-only performance monitor registers' encodings.
 * See Arm Architecture Reference Manual Armv8-A, D12.3.1.
 * NAME, op0, op1, crn, crm, op2
 */
#define PERFMON_REGISTERS_WRITE                \
	X(PMSWINC_EL0       , 3, 3,  9, 12, 4) \

/**
 * Definitions of readable and writeable performance monitor registers' encodings.
 * See Arm Architecture Reference Manual Armv8-A, D12.3.1.
 * NAME, op0, op1, crn, crm, op2
 */
#define PERFMON_REGISTERS_READ_WRITE           \
	X(PMINTENSET_EL1    , 3, 0,  9, 14, 1) \
	X(PMINTENCLR_EL1    , 3, 0,  9, 14, 2) \
	X(PMCR_EL0          , 3, 3,  9, 12, 0) \
	X(PMCNTENSET_EL0    , 3, 3,  9, 12, 1) \
	X(PMCNTENCLR_EL0    , 3, 3,  9, 12, 2) \
	X(PMOVSCLR_EL0      , 3, 3,  9, 12, 3) \
	X(PMSELR_EL0        , 3, 3,  9, 12, 5) \
	X(PMCCNTR_EL0       , 3, 3,  9, 13, 0) \
	X(PMXEVTYPER_EL0    , 3, 3,  9, 13, 1) \
	X(PMXEVCNTR_EL0     , 3, 3,  9, 13, 2) \
	X(PMUSERENR_EL0     , 3, 3,  9, 14, 0) \
	X(PMOVSSET_EL0      , 3, 3,  9, 14, 3) \
	X(PMEVTYPER0_EL0    , 3, 3, 14, 12, 0) \
	X(PMEVTYPER1_EL0    , 3, 3, 14, 12, 1) \
	X(PMEVTYPER2_EL0    , 3, 3, 14, 12, 2) \
	X(PMEVTYPER3_EL0    , 3, 3, 14, 12, 3) \
	X(PMEVTYPER4_EL0    , 3, 3, 14, 12, 4) \
	X(PMEVTYPER5_EL0    , 3, 3, 14, 12, 5) \
	X(PMEVTYPER6_EL0    , 3, 3, 14, 12, 6) \
	X(PMEVTYPER7_EL0    , 3, 3, 14, 12, 7) \
	X(PMEVTYPER8_EL0    , 3, 3, 14, 13, 0) \
	X(PMEVTYPER9_EL0    , 3, 3, 14, 13, 1) \
	X(PMEVTYPER10_EL0   , 3, 3, 14, 13, 2) \
	X(PMEVTYPER11_EL0   , 3, 3, 14, 13, 3) \
	X(PMEVTYPER12_EL0   , 3, 3, 14, 13, 4) \
	X(PMEVTYPER13_EL0   , 3, 3, 14, 13, 5) \
	X(PMEVTYPER14_EL0   , 3, 3, 14, 13, 6) \
	X(PMEVTYPER15_EL0   , 3, 3, 14, 13, 7) \
	X(PMEVTYPER16_EL0   , 3, 3, 14, 14, 0) \
	X(PMEVTYPER17_EL0   , 3, 3, 14, 14, 1) \
	X(PMEVTYPER18_EL0   , 3, 3, 14, 14, 2) \
	X(PMEVTYPER19_EL0   , 3, 3, 14, 14, 3) \
	X(PMEVTYPER20_EL0   , 3, 3, 14, 14, 4) \
	X(PMEVTYPER21_EL0   , 3, 3, 14, 14, 5) \
	X(PMEVTYPER22_EL0   , 3, 3, 14, 14, 6) \
	X(PMEVTYPER23_EL0   , 3, 3, 14, 14, 7) \
	X(PMEVTYPER24_EL0   , 3, 3, 14, 15, 0) \
	X(PMEVTYPER25_EL0   , 3, 3, 14, 15, 1) \
	X(PMEVTYPER26_EL0   , 3, 3, 14, 15, 2) \
	X(PMEVTYPER27_EL0   , 3, 3, 14, 15, 3) \
	X(PMEVTYPER28_EL0   , 3, 3, 14, 15, 4) \
	X(PMEVTYPER29_EL0   , 3, 3, 14, 15, 5) \
	X(PMEVTYPER30_EL0   , 3, 3, 14, 15, 6) \
	X(PMCCFILTR_EL0     , 3, 3, 14, 15, 7)

/* clang-format on */

/**
 * Returns true if the ESR register shows an access to a performance monitor
 * register.
 */
bool perfmon_is_register_access(uintreg_t esr)
{
	uintreg_t op0 = GET_ISS_OP0(esr);
	uintreg_t op1 = GET_ISS_OP1(esr);
	uintreg_t crn = GET_ISS_CRN(esr);
	uintreg_t crm = GET_ISS_CRM(esr);

	/* From the Arm Architecture Reference Manual Table D12-2. */

	/* For PMINTENCLR_EL1 and PMINTENSET_EL1*/
	if (op0 == 3 && op1 == 0 && crn == 9 && crm == 14) {
		return true;
	}

	/* For PMEVCNTRn_EL0, PMEVTYPERn_EL0, and PMCCFILTR_EL0. */
	if (op0 == 3 && op1 == 3 && crn == 14 && crm >= 8 && crm <= 15) {
		return true;
	}

	/* For all remaining performance monitor registers. */
	return op0 == 3 && op1 == 3 && crn == 9 && crm >= 12 && crm <= 14;
}

/**
 * Processes an access (msr, mrs) to a performance monitor register.
 * Returns true if the access was allowed and performed, false otherwise.
 */
bool perfmon_process_access(struct vcpu *vcpu, spci_vm_id_t vm_id,
			    uintreg_t esr)
{
	/*
	 * For now, performance monitor registers are not supported by secondary
	 * VMs. Disallow accesses to them.
	 */
	if (vm_id != HF_PRIMARY_VM_ID) {
		return false;
	}

	uintreg_t sys_register = GET_ISS_SYSREG(esr);
	uintreg_t rt_register = GET_ISS_RT(esr);
	uintreg_t value;

	/* +1 because Rt can access register XZR */
	CHECK(rt_register < NUM_GP_REGS + 1);

	if (ISS_IS_READ(esr)) {
		switch (sys_register) {
#define X(reg_name, op0, op1, crn, crm, op2)              \
	case (GET_ISS_ENCODING(op0, op1, crn, crm, op2)): \
		value = read_msr(reg_name);               \
		break;
			PERFMON_REGISTERS_READ
			PERFMON_REGISTERS_READ_WRITE
#undef X
		default:
			value = vcpu->regs.r[rt_register];
			dlog("Unsupported performance monitor register read: "
			     "op0=%d, op1=%d, crn=%d, crm=%d, op2=%d, rt=%d.\n",
			     GET_ISS_OP0(esr), GET_ISS_OP1(esr),
			     GET_ISS_CRN(esr), GET_ISS_CRM(esr),
			     GET_ISS_OP2(esr), GET_ISS_RT(esr));
			break;
		}
		if (rt_register != RT_REG_XZR) {
			vcpu->regs.r[rt_register] = value;
		}
	} else {
		if (rt_register != RT_REG_XZR) {
			value = vcpu->regs.r[rt_register];
		} else {
			value = 0;
		}
		switch (sys_register) {
#define X(reg_name, op0, op1, crn, crm, op2)              \
	case (GET_ISS_ENCODING(op0, op1, crn, crm, op2)): \
		write_msr(reg_name, value);               \
		break;
			PERFMON_REGISTERS_WRITE
			PERFMON_REGISTERS_READ_WRITE
#undef X
		default:
			dlog("Unsupported performance monitor register write: "
			     "op0=%d, op1=%d, crn=%d, crm=%d, op2=%d, rt=%d.\n",
			     GET_ISS_OP0(esr), GET_ISS_OP1(esr),
			     GET_ISS_CRN(esr), GET_ISS_CRM(esr),
			     GET_ISS_OP2(esr), GET_ISS_RT(esr));
			break;
		}
	}

	return true;
}

/**
 * Returns the value register PMCCFILTR_EL0 should have at initialization.
 */
uintreg_t perfmon_get_pmccfiltr_el0_init_value(spci_vm_id_t vm_id)
{
	if (vm_id != HF_PRIMARY_VM_ID) {
		/* Disable cycle counting for secondary VMs. */
		return PMCCFILTR_EL0_P | PMCCFILTR_EL0_U;
	}

	return 0;
}
