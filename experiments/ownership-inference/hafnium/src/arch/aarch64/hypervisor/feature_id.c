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

#include "feature_id.h"

#include "hf/check.h"
#include "hf/dlog.h"
#include "hf/types.h"
#include "hf/vm.h"

#include "msr.h"
#include "sysregs.h"

/* clang-format off */

/**
 * Definitions of read-only feature ID (group 3) registers' encodings.
 * See Arm Architecture Reference Manual Armv8-A, Table D1-52 and D12-2.
 * NAME, op0, op1, crn, crm, op2
 */
#define FEATURE_ID_REGISTERS_READ              \
	X(ID_PFR0_EL1       , 3, 0,  0,  1, 0) \
	X(ID_PFR1_EL1       , 3, 0,  0,  1, 1) \
	X(ID_DFR0_EL1       , 3, 0,  0,  1, 2) \
	X(ID_AFR0_EL1       , 3, 0,  0,  1, 3) \
	X(ID_MMFR0_EL1      , 3, 0,  0,  1, 4) \
	X(ID_MMFR1_EL1      , 3, 0,  0,  1, 5) \
	X(ID_MMFR2_EL1      , 3, 0,  0,  1, 6) \
	X(ID_MMFR3_EL1      , 3, 0,  0,  1, 7) \
	X(ID_ISAR0_EL1      , 3, 0,  0,  2, 0) \
	X(ID_ISAR1_EL1      , 3, 0,  0,  2, 1) \
	X(ID_ISAR2_EL1      , 3, 0,  0,  2, 2) \
	X(ID_ISAR3_EL1      , 3, 0,  0,  2, 3) \
	X(ID_ISAR4_EL1      , 3, 0,  0,  2, 4) \
	X(ID_ISAR5_EL1      , 3, 0,  0,  2, 5) \
	X(ID_MMFR4_EL1      , 3, 0,  0,  2, 6) \
	\
	X(MVFR0_EL1         , 3, 0,  0,  3, 0) \
	X(MVFR1_EL1         , 3, 0,  0,  3, 1) \
	X(MVFR2_EL1         , 3, 0,  0,  3, 2) \
	\
	X(ID_AA64PFR0_EL1   , 3, 0,  0,  4, 0) \
	X(ID_AA64PFR1_EL1   , 3, 0,  0,  4, 1) \
	\
	X(ID_AA64DFR0_EL1   , 3, 0,  0,  5, 0) \
	X(ID_AA64DFR1_EL1   , 3, 0,  0,  5, 1) \
	\
	X(ID_AA64AFR0_EL1   , 3, 0,  0,  5, 4) \
	X(ID_AA64AFR1_EL1   , 3, 0,  0,  5, 5) \
	\
	X(ID_AA64ISAR0_EL1  , 3, 0,  0,  6, 0) \
	X(ID_AA64ISAR1_EL1  , 3, 0,  0,  6, 1) \
	\
	X(ID_AA64MMFR0_EL1  , 3, 0,  0,  7, 0) \
	X(ID_AA64MMFR1_EL1  , 3, 0,  0,  7, 1) \
	X(ID_AA64MMFR2_EL1  , 3, 0,  0,  7, 2)

/* clang-format on */

enum {
#define X(reg_name, op0, op1, crn, crm, op2) \
	reg_name##_ENC = GET_ISS_ENCODING(op0, op1, crn, crm, op2),
	FEATURE_ID_REGISTERS_READ
#undef X
};

/**
 * Returns true if the ESR register shows an access to a feature ID group 3
 * register.
 */
bool feature_id_is_register_access(uintreg_t esr)
{
	uintreg_t op0 = GET_ISS_OP0(esr);
	uintreg_t op1 = GET_ISS_OP1(esr);
	uintreg_t crn = GET_ISS_CRN(esr);
	uintreg_t crm = GET_ISS_CRM(esr);

	/* From the Arm Architecture Reference Manual Table D12-2. */
	return op0 == 3 && op1 == 0 && crn == 0 && crm >= 1 && crm <= 7;
}

/**
 * RAS-related. RES0 when RAS is not implemented.
 */
#define ID_AA64MMFR1_EL1_SPEC_SEI (UINT64_C(0xf) << 24)

/**
 * Indicates support for LORegions.
 */
#define ID_AA64MMFR1_EL1_LO (UINT64_C(0xf) << 24)

/**
 * RAS Extension version.
 */
#define ID_AA64PFR0_EL1_RAS (UINT64_C(0xf) << 28)

/**
 * Self-hosted Trace Extension Version
 */
#define ID_AA64DFR0_EL1_TRACE_FILT (UINT64_C(0xf) << 40)

/**
 * OS Double Lock implemented.
 */
#define ID_AA64DFR0_EL1_DOUBLE_LOCK (UINT64_C(0xf) << 36)

/**
 * Statistical Profiling Extension version.
 */
#define ID_AA64DFR0_EL1_PMS_VER (UINT64_C(0xf) << 32)

/**
 * Performance Monitors Extension version.
 */
#define ID_AA64DFR0_EL1_PMU_VER (UINT64_C(0xf) << 8)

/**
 * Indicates whether System register interface to trace unit is implemented.
 */
#define ID_AA64DFR0_EL1_TRACE_VER (UINT64_C(0xf) << 4)

/**
 * Debug architecture version.
 */
#define ID_AA64DFR0_EL1_DEBUG_VER (UINT64_C(0xf))

/**
 * PAuth: whether an implementation defined algorithm for generic code
 * authentication is implemented.
 */
#define ID_AA64ISAR1_EL1_GPI (UINT64_C(0xf) << 28)

/**
 * PAuth: whether QARMA or Architected algorithm for generic code authentication
 * is implemented.
 */
#define ID_AA64ISAR1_EL1_GPA (UINT64_C(0xf) << 24)

/**
 * PAuth: whether an implementation defined algorithm for address authentication
 * is implemented.
 */
#define ID_AA64ISAR1_EL1_API (UINT64_C(0xf) << 8)

/**
 * PAuth: whether QARMA or Architected algorithm for address authentication is
 * implemented.
 */
#define ID_AA64ISAR1_EL1_APA (UINT64_C(0xf) << 24)

void feature_set_traps(struct vm *vm, struct arch_regs *regs)
{
	arch_features_t features = vm->arch.trapped_features;

	if (features & ~HF_FEATURE_ALL) {
		panic("features has undefined bits 0x%x", features);
	}

	/* By default do not mask out any features. */
	vm->arch.tid3_masks.id_aa64mmfr1_el1 = ~0ULL;
	vm->arch.tid3_masks.id_aa64pfr0_el1 = ~0ULL;
	vm->arch.tid3_masks.id_aa64dfr0_el1 = ~0ULL;
	vm->arch.tid3_masks.id_aa64isar1_el1 = ~0ULL;

	if (features & HF_FEATURE_RAS) {
		regs->lazy.hcr_el2 |= HCR_EL2_TERR;
		vm->arch.tid3_masks.id_aa64mmfr1_el1 &=
			~ID_AA64MMFR1_EL1_SPEC_SEI;
		vm->arch.tid3_masks.id_aa64pfr0_el1 &= ~ID_AA64PFR0_EL1_RAS;
	}

	if (features & HF_FEATURE_SPE) {
		/*
		 * Trap VM accesses to Statistical Profiling Extension (SPE)
		 * registers.
		 */
		regs->lazy.mdcr_el2 |= MDCR_EL2_TPMS;

		/*
		 * Set E2PB to 0b00. This ensures that accesses to Profiling
		 * Buffer controls at EL1 are trapped to EL2.
		 */
		regs->lazy.mdcr_el2 &= ~MDCR_EL2_E2PB;

		vm->arch.tid3_masks.id_aa64dfr0_el1 &= ~ID_AA64DFR0_EL1_PMS_VER;
	}

	if (features & HF_FEATURE_DEBUG) {
		regs->lazy.mdcr_el2 |=
			MDCR_EL2_TDRA | MDCR_EL2_TDOSA | MDCR_EL2_TDA;

		vm->arch.tid3_masks.id_aa64dfr0_el1 &=
			~ID_AA64DFR0_EL1_DOUBLE_LOCK;
	}

	if (features & HF_FEATURE_TRACE) {
		regs->lazy.mdcr_el2 |= MDCR_EL2_TTRF;

		vm->arch.tid3_masks.id_aa64dfr0_el1 &=
			~ID_AA64DFR0_EL1_TRACE_FILT;
		vm->arch.tid3_masks.id_aa64dfr0_el1 &=
			~ID_AA64DFR0_EL1_TRACE_VER;
	}

	if (features & HF_FEATURE_PERFMON) {
		regs->lazy.mdcr_el2 |= MDCR_EL2_TPM | MDCR_EL2_TPMCR;

		vm->arch.tid3_masks.id_aa64dfr0_el1 &= ~ID_AA64DFR0_EL1_PMU_VER;
	}

	if (features & HF_FEATURE_LOR) {
		regs->lazy.hcr_el2 |= HCR_EL2_TLOR;

		vm->arch.tid3_masks.id_aa64mmfr1_el1 &= ~ID_AA64MMFR1_EL1_LO;
	}

	if (features & HF_FEATURE_PAUTH) {
		/* APK and API bits *enable* trapping when cleared. */
		regs->lazy.hcr_el2 &= ~(HCR_EL2_APK | HCR_EL2_API);

		vm->arch.tid3_masks.id_aa64isar1_el1 &= ~ID_AA64ISAR1_EL1_GPI;
		vm->arch.tid3_masks.id_aa64isar1_el1 &= ~ID_AA64ISAR1_EL1_GPA;
		vm->arch.tid3_masks.id_aa64isar1_el1 &= ~ID_AA64ISAR1_EL1_API;
		vm->arch.tid3_masks.id_aa64isar1_el1 &= ~ID_AA64ISAR1_EL1_APA;
	}
}

/**
 * Processes an access (mrs) to a feature ID register.
 * Returns true if the access was allowed and performed, false otherwise.
 */
bool feature_id_process_access(struct vcpu *vcpu, uintreg_t esr)
{
	const struct vm *vm = vcpu->vm;
	uintreg_t sys_register = GET_ISS_SYSREG(esr);
	uintreg_t rt_register = GET_ISS_RT(esr);
	uintreg_t value;

	/* +1 because Rt can access register XZR */
	CHECK(rt_register < NUM_GP_REGS + 1);

	if (!ISS_IS_READ(esr)) {
		dlog("Unsupported feature ID register write: "
		     "op0=%d, op1=%d, crn=%d, crm=%d, op2=%d, rt=%d.\n",
		     GET_ISS_OP0(esr), GET_ISS_OP1(esr), GET_ISS_CRN(esr),
		     GET_ISS_CRM(esr), GET_ISS_OP2(esr), GET_ISS_RT(esr));
		return true;
	}

	switch (sys_register) {
#define X(reg_name, op0, op1, crn, crm, op2)              \
	case (GET_ISS_ENCODING(op0, op1, crn, crm, op2)): \
		value = read_msr(reg_name);               \
		break;
		FEATURE_ID_REGISTERS_READ
#undef X
	default:
		/* Reserved registers should be read as zero (raz). */
		value = 0;
		dlog("Unsupported feature ID register read: "
		     "op0=%d, op1=%d, crn=%d, crm=%d, op2=%d, rt=%d.\n",
		     GET_ISS_OP0(esr), GET_ISS_OP1(esr), GET_ISS_CRN(esr),
		     GET_ISS_CRM(esr), GET_ISS_OP2(esr), GET_ISS_RT(esr));
		break;
	}

	/* Mask values for features Hafnium might restrict. */
	switch (sys_register) {
	case ID_AA64MMFR1_EL1_ENC:
		value &= vm->arch.tid3_masks.id_aa64mmfr1_el1;
		break;
	case ID_AA64PFR0_EL1_ENC:
		value &= vm->arch.tid3_masks.id_aa64pfr0_el1;
		break;
	case ID_AA64DFR0_EL1_ENC:
		value &= vm->arch.tid3_masks.id_aa64dfr0_el1;
		break;
	case ID_AA64ISAR1_EL1_ENC:
		value &= vm->arch.tid3_masks.id_aa64isar1_el1;
		break;
	default:
		break;
	}

	if (rt_register != RT_REG_XZR) {
		vcpu->regs.r[rt_register] = value;
	}

	return true;
}
