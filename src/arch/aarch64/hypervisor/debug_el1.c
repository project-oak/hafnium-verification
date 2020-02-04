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

#include "debug_el1.h"

#include "hf/check.h"
#include "hf/dlog.h"
#include "hf/panic.h"
#include "hf/types.h"

#include "msr.h"

/**
 * Controls traps for Trace Filter.
 */
#define MDCR_EL2_TTRF (0x1u << 19)

/**
 * Controls the owning translation regime and access to Profiling Buffer control
 * registers from EL1. Depends on whether SPE is implemented.
 */
#define MDCR_EL2_E2PB (0x3u << 12)

/**
 * Controls traps for Debug ROM.
 */
#define MDCR_EL2_TDRA (0x1u << 11)

/**
 * Controls traps for OS-Related Register Access.
 */
#define MDCR_EL2_TDOSA (0x1u << 10)

/**
 * Controls traps for remaining Debug Registers not trapped by TDRA and TDOSA.
 */
#define MDCR_EL2_TDA (0x1u << 9)

/**
 * Controls traps for all debug exceptions (e.g., breakpoints).
 */
#define MDCR_EL2_TDE (0x1u << 8)

/**
 * Defines the number of event counters that are accessible from various
 * exception levels, if permitted.  Dependant on whether PMUv3 is implemented.
 */
#define MDCR_EL2_HPMN (0x1fu << 0)

/**
 * Controls traps for debug events, i.e., breakpoints, watchpoints, and vector.
 * catch exceptions.
 */
#define MDSCR_EL1_MDE (0x1u << 15)

/**
 * System register are identified by op0, op2, op1, crn, crm. The ISS encoding
 * includes also rt and direction. Exclude them,  @see D13.2.37 (D13-2977).
 */
#define ISS_SYSREG_MASK                               \
	(((1u << 22) - 1u) & /* Select the ISS bits*/ \
	 ~(0x1fu << 5) &     /* exclude rt */         \
	 ~1u /* exclude direction */)

#define GET_ISS_SYSREG(esr) (ISS_SYSREG_MASK & (esr))

/**
 * Op0 from the ISS encoding in the ESR.
 */
#define ISS_OP0_MASK 0x300000
#define ISS_OP0_SHIFT 20
#define GET_ISS_OP0(esr) ((ISS_OP0_MASK & (esr)) >> ISS_OP0_SHIFT)

/**
 * Op1 from the ISS encoding in the ESR.
 */
#define ISS_OP1_MASK 0x1c000
#define ISS_OP1_SHIFT 14
#define GET_ISS_OP1(esr) ((ISS_OP1_MASK & (esr)) >> ISS_OP1_SHIFT)

/**
 * Direction (i.e., read (1) or write (0), is the first bit in the ISS/ESR.
 */
#define ISS_DIRECTION_MASK 1u

/**
 * Gets the direction of the system register access, read (1) or write (0).
 */
#define GET_ISS_DIRECTION(esr) (ISS_DIRECTION_MASK & (esr))

/**
 * True if the ISS encoded in the esr indicates a read of the system register.
 */
#define ISS_IS_READ(esr) (ISS_DIRECTION_MASK & (esr))

/**
 * Rt, which identifies the general purpose register used for the operation.
 */
#define ISS_RT_MASK 0x3e0
#define ISS_RT_SHIFT 5
#define GET_ISS_RT(esr) ((ISS_RT_MASK & (esr)) >> ISS_RT_SHIFT)

/**
 * PMCR_EL0.N: Indicates the number of event counters implemented.
 */
#define PMCR_EL0_N_MASK 0xf800
#define PMCR_EL0_N_SHIFT 11
#define GET_PMCR_EL0_N(pmcr) ((PMCR_EL0_N_MASK & (pmcr)) >> PMCR_EL0_N_SHIFT)

/**
 * Definitions of read-only debug registers' ISS signatures.
 */
#define EL1_DEBUG_REGISTERS_READ       \
	X(MDRAR_EL1, 0x200400)         \
	X(DBGAUTHSTATUS_EL1, 0x2c1c1c) \
	X(OSLSR_EL1, 0x280402)

/**
 * Definitions of readable and writeable debug registers' ISS signatures.
 */
#define EL1_DEBUG_REGISTERS_READ_WRITE \
	X(DBGCLAIMCLR_EL1, 0x2c1c12)   \
	X(DBGCLAIMSET_EL1, 0x2c1c10)   \
	X(DBGPRCR_EL1, 0x280408)       \
	X(MDCCINT_EL1, 0x200004)       \
	X(MDSCR_EL1, 0x240004)         \
	X(OSDLR_EL1, 0x280406)         \
	X(OSDTRRX_EL1, 0x240000)       \
	X(OSDTRTX_EL1, 0x240006)       \
	X(OSECCR_EL1, 0x24000c)        \
	X(DBGBCR0_EL1, 0x2a0000)       \
	X(DBGBCR1_EL1, 0x2a0002)       \
	X(DBGBCR2_EL1, 0x2a0004)       \
	X(DBGBCR3_EL1, 0x2a0006)       \
	X(DBGBCR4_EL1, 0x2a0008)       \
	X(DBGBCR5_EL1, 0x2a000a)       \
	X(DBGBCR6_EL1, 0x2a000c)       \
	X(DBGBCR7_EL1, 0x2a000e)       \
	X(DBGBCR8_EL1, 0x2a0010)       \
	X(DBGBCR9_EL1, 0x2a0012)       \
	X(DBGBCR10_EL1, 0x2a0014)      \
	X(DBGBCR11_EL1, 0x2a0016)      \
	X(DBGBCR12_EL1, 0x2a0018)      \
	X(DBGBCR13_EL1, 0x2a001a)      \
	X(DBGBCR14_EL1, 0x2a001c)      \
	X(DBGBCR15_EL1, 0x2a001e)      \
	X(DBGBVR0_EL1, 0x280000)       \
	X(DBGBVR1_EL1, 0x280002)       \
	X(DBGBVR2_EL1, 0x280004)       \
	X(DBGBVR3_EL1, 0x280006)       \
	X(DBGBVR4_EL1, 0x280008)       \
	X(DBGBVR5_EL1, 0x28000a)       \
	X(DBGBVR6_EL1, 0x28000c)       \
	X(DBGBVR7_EL1, 0x28000e)       \
	X(DBGBVR8_EL1, 0x280010)       \
	X(DBGBVR9_EL1, 0x280012)       \
	X(DBGBVR10_EL1, 0x280014)      \
	X(DBGBVR11_EL1, 0x280016)      \
	X(DBGBVR12_EL1, 0x280018)      \
	X(DBGBVR13_EL1, 0x28001a)      \
	X(DBGBVR14_EL1, 0x28001c)      \
	X(DBGBVR15_EL1, 0x28001e)      \
	X(DBGWCR0_EL1, 0x2e0000)       \
	X(DBGWCR1_EL1, 0x2e0002)       \
	X(DBGWCR2_EL1, 0x2e0004)       \
	X(DBGWCR3_EL1, 0x2e0006)       \
	X(DBGWCR4_EL1, 0x2e0008)       \
	X(DBGWCR5_EL1, 0x2e000a)       \
	X(DBGWCR6_EL1, 0x2e000c)       \
	X(DBGWCR7_EL1, 0x2e000e)       \
	X(DBGWCR8_EL1, 0x2e0010)       \
	X(DBGWCR9_EL1, 0x2e0012)       \
	X(DBGWCR10_EL1, 0x2e0014)      \
	X(DBGWCR11_EL1, 0x2e0016)      \
	X(DBGWCR12_EL1, 0x2e0018)      \
	X(DBGWCR13_EL1, 0x2e001a)      \
	X(DBGWCR14_EL1, 0x2e001c)      \
	X(DBGWCR15_EL1, 0x2e001e)      \
	X(DBGWVR0_EL1, 0x2c0000)       \
	X(DBGWVR1_EL1, 0x2c0002)       \
	X(DBGWVR2_EL1, 0x2c0004)       \
	X(DBGWVR3_EL1, 0x2c0006)       \
	X(DBGWVR4_EL1, 0x2c0008)       \
	X(DBGWVR5_EL1, 0x2c000a)       \
	X(DBGWVR6_EL1, 0x2c000c)       \
	X(DBGWVR7_EL1, 0x2c000e)       \
	X(DBGWVR8_EL1, 0x2c0010)       \
	X(DBGWVR9_EL1, 0x2c0012)       \
	X(DBGWVR10_EL1, 0x2c0014)      \
	X(DBGWVR11_EL1, 0x2c0016)      \
	X(DBGWVR12_EL1, 0x2c0018)      \
	X(DBGWVR13_EL1, 0x2c001a)      \
	X(DBGWVR14_EL1, 0x2c001c)      \
	X(DBGWVR15_EL1, 0x2c001e)

/**
 * Definitions of all debug registers' ISS signatures.
 */
#define EL1_DEBUG_REGISTERS      \
	EL1_DEBUG_REGISTERS_READ \
	EL1_DEBUG_REGISTERS_READ_WRITE

/**
 * Returns the value for MDCR_EL2 for the particular VM.
 * For now, the primary VM has one value and all secondary VMs share a value.
 */
uintreg_t get_mdcr_el2_value(spci_vm_id_t vm_id)
{
	uintreg_t mdcr_el2_value = read_msr(MDCR_EL2);
	uintreg_t pmcr_el0 = read_msr(PMCR_EL0);

	/*
	 * Preserve E2PB for now, which depends on the SPE implementation.
	 * TODO: Investigate how to detect whether SPE is implemented, and which
	 * stage's translation regime is applicable, i.e., EL2 or EL1.
	 */
	mdcr_el2_value &= MDCR_EL2_E2PB;

	/*
	 * Set the number of event counters accessible from all exception levels
	 * (MDCR_EL2.HPMN) to be the number of implemented event counters
	 * (PMCR_EL0.N).
	 * TODO(b/132394973): examine the implications of this setting.
	 */
	mdcr_el2_value |= GET_PMCR_EL0_N(pmcr_el0) & MDCR_EL2_HPMN;

	/*
	 * Trap all VM accesses to debug registers to have fine grained control
	 * over system register accesses.
	 * Do not trap the Primary VM's debug events, e.g., watchpoint or
	 * breakpoint events (!MDCR_EL2_TDE).
	 */
	mdcr_el2_value |=
		MDCR_EL2_TTRF | MDCR_EL2_TDRA | MDCR_EL2_TDOSA | MDCR_EL2_TDA;

	if (vm_id != HF_PRIMARY_VM_ID) {
		/*
		 * Debug event exceptions should be disabled in secondary VMs
		 * but trap them for additional security.
		 */
		mdcr_el2_value |= MDCR_EL2_TDE;
	}

	return mdcr_el2_value;
}

/**
 * Returns true if the ESR register shows an access to an EL1 debug register.
 */
bool is_debug_el1_register_access(uintreg_t esr_el2)
{
	/*
	 * Architecture Reference Manual D12.2: op0 == 0b10 is for debug and
	 * trace system registers.  op1 = 0x1 for trace, remaining are debug.
	 */
	return GET_ISS_OP0(esr_el2) == 0x2 && GET_ISS_OP1(esr_el2) != 0x1;
}

/**
 * Processes an access (msr, mrs) to an EL1 debug register.
 * Returns true if the access was allowed and performed, false otherwise.
 */
bool debug_el1_process_access(struct vcpu *vcpu, spci_vm_id_t vm_id,
			      uintreg_t esr_el2)
{
	/*
	 * For now, debug registers are not supported by secondary VMs.
	 * Disallow accesses to them.
	 */
	if (vm_id != HF_PRIMARY_VM_ID) {
		return false;
	}

	uintreg_t sys_register = GET_ISS_SYSREG(esr_el2);
	uintreg_t rt_register = GET_ISS_RT(esr_el2);
	uintreg_t value;

	CHECK(rt_register < NUM_GP_REGS);

	if (ISS_IS_READ(esr_el2)) {
		switch (sys_register) {
#define X(reg_name, reg_sig)                \
	case reg_sig:                       \
		value = read_msr(reg_name); \
		break;
			EL1_DEBUG_REGISTERS
#undef X
		default:
			value = vcpu_get_regs(vcpu)->r[rt_register];
			dlog("Unsupported system register read 0x%x\n",
			     sys_register);
			break;
		}
		vcpu_get_regs(vcpu)->r[rt_register] = value;

	} else {
		value = vcpu_get_regs(vcpu)->r[rt_register];
		switch (sys_register) {
#define X(reg_name, reg_sig)                \
	case reg_sig:                       \
		write_msr(reg_name, value); \
		break;
			EL1_DEBUG_REGISTERS_READ_WRITE
#undef X
		default:
			dlog("Unsupported system register write 0x%x\n",
			     sys_register);
			break;
		}
	}

	return true;
}
