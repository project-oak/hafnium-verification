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

#pragma once

#include "hf/arch/types.h"

#include "hf/cpu.h"

#include "vmapi/hf/spci.h"

/**
 * RT value that indicates an access to register XZR (always 0).
 * See Arm Architecture Reference Manual Armv8-A, C1.2.5
 */
#define RT_REG_XZR (UINT64_C(31))

/**
 * Hypervisor (EL2) Cycle Count Disable.
 */
#define MDCR_EL2_HCCD (UINT64_C(0x1) << 23)

/**
 * Controls traps for Trace Filter when Self-hosted Trace is implemented.
 */
#define MDCR_EL2_TTRF (UINT64_C(0x1) << 19)

/**
 * Hypervisor (EL2) Event Count Disable.
 */
#define MDCR_EL2_HPMD (UINT64_C(0x1) << 17)

/**
 * Trap Performance Monitor Sampling.
 * Traps access to Statistical Profiling control registers from EL1 when
 * the Statistical Profiling Extension (SPE) is implemented.
 */
#define MDCR_EL2_TPMS (UINT64_C(0x1) << 14)

/**
 * Controls the owning translation regime and access to Profiling Buffer control
 * registers from EL1. Depends on whether SPE is implemented.
 */
#define MDCR_EL2_E2PB (UINT64_C(0x3) << 12)

/**
 * Controls traps for Debug ROM.
 */
#define MDCR_EL2_TDRA (UINT64_C(0x1) << 11)

/**
 * Controls traps for debug OS-Related Register accesses when DoubleLock is
 * implemented.
 */
#define MDCR_EL2_TDOSA (UINT64_C(0x1) << 10)

/**
 * Controls traps for remaining Debug Registers not trapped by TDRA and TDOSA.
 */
#define MDCR_EL2_TDA (UINT64_C(0x1) << 9)

/**
 * Controls traps for all debug exceptions (e.g., breakpoints).
 */
#define MDCR_EL2_TDE (UINT64_C(0x1) << 8)

/**
 * Controls traps for all performance monitor register accesses other than
 * PMCR_EL0.
 */
#define MDCR_EL2_TPM (UINT64_C(0x1) << 6)

/**
 * Controls traps for performance monitor register PMCR_EL0.
 */
#define MDCR_EL2_TPMCR (UINT64_C(0x1) << 5)

/**
 * Defines the number of event counters that are accessible from various
 * exception levels, if permitted. Dependant on whether PMUv3
 * is implemented.
 */
#define MDCR_EL2_HPMN (UINT64_C(0x1f) << 0)

/*
 * Definitions for interpreting the ESR_ELx registers.
 * See Arm Architecture Reference Manual Armv8-A, D13.2.36 and D13.2.37.
 */

/**
 * Offset for the Exception Class (EC) field in the ESR.
 */
#define ESR_EC_OFFSET UINT64_C(26)

/**
 * Gets the Exception Class from the ESR.
 */
#define GET_ESR_EC(esr) ((esr) >> ESR_EC_OFFSET)

/**
 * Gets the Instruction Length bit for the synchronous exception
 */
#define GET_ESR_IL(esr) ((esr) & (1 << 25))

/**
 * ESR code for an Unknown Reason exception.
 */
#define EC_UNKNOWN UINT64_C(0x0)

/**
 * ESR code for trapped WFI or WFE instruction execution.
 */
#define EC_WFI_WFE UINT64_C(0x1)

/**
 * ESR code for HVC instruction execution.
 */
#define EC_HVC UINT64_C(0x16)

/**
 * ESR code for SMC instruction execution.
 */
#define EC_SMC UINT64_C(0x17)

/**
 * ESR code for MSR, MRS, or System instruction execution.
 */
#define EC_MSR UINT64_C(0x18)

/**
 * ESR code for Instruction Abort from a lower Exception level.
 */
#define EC_INSTRUCTION_ABORT_LOWER_EL UINT64_C(0x20)

/**
 * ESR code for Instruction Abort without a change in Exception level.
 */
#define EC_INSTRUCTION_ABORT_SAME_EL UINT64_C(0x21)

/**
 * ESR code for Data Abort from a lower Exception level.
 */
#define EC_DATA_ABORT_LOWER_EL UINT64_C(0x24)

/**
 * ESR code for Data Abort without a change in Exception level.
 */
#define EC_DATA_ABORT_SAME_EL UINT64_C(0x25)

/**
 * Mask for ISS bits in ESR_ELx registers.
 */
#define ISS_MASK ((UINT64_C(0x1) << 22) - UINT64_C(0x1))

#define GET_ESR_ISS(esr) (ISS_MASK & (esr))

/**
 * System register are identified by op0, op2, op1, crn, crm. The ISS encoding
 * includes also rt and direction. Exclude them, @see D13.2.37 (D13-2977).
 */
#define ISS_SYSREG_MASK                                     \
	(ISS_MASK &		  /* Select the ISS bits */ \
	 ~(UINT64_C(0x1f) << 5) & /* exclude rt */          \
	 ~UINT64_C(0x1) /* exclude direction */)

#define GET_ISS_SYSREG(esr) (ISS_SYSREG_MASK & (esr))

/**
 * Op0 from the ISS encoding in the ESR.
 */
#define ISS_OP0_MASK UINT64_C(0x300000)
#define ISS_OP0_SHIFT 20
#define GET_ISS_OP0(esr) ((ISS_OP0_MASK & (esr)) >> ISS_OP0_SHIFT)

/**
 * Op1 from the ISS encoding in the ESR.
 */
#define ISS_OP1_MASK UINT64_C(0x1c000)
#define ISS_OP1_SHIFT 14
#define GET_ISS_OP1(esr) ((ISS_OP1_MASK & (esr)) >> ISS_OP1_SHIFT)

/**
 * Op2 from the ISS encoding in the ESR.
 */
#define ISS_OP2_MASK UINT64_C(0xe0000)
#define ISS_OP2_SHIFT 17
#define GET_ISS_OP2(esr) ((ISS_OP2_MASK & (esr)) >> ISS_OP2_SHIFT)

/**
 * CRn from the ISS encoding in the ESR.
 */
#define ISS_CRN_MASK UINT64_C(0x3c00)
#define ISS_CRN_SHIFT 10
#define GET_ISS_CRN(esr) ((ISS_CRN_MASK & (esr)) >> ISS_CRN_SHIFT)

/**
 * CRm from the ISS encoding in the ESR.
 */
#define ISS_CRM_MASK UINT64_C(0x1e)
#define ISS_CRM_SHIFT 1
#define GET_ISS_CRM(esr) ((ISS_CRM_MASK & (esr)) >> ISS_CRM_SHIFT)

/**
 * Rt, which identifies the general purpose register used for the operation.
 */
#define ISS_RT_MASK UINT64_C(0x3e0)
#define ISS_RT_SHIFT 5
#define GET_ISS_RT(esr) ((ISS_RT_MASK & (esr)) >> ISS_RT_SHIFT)

/**
 * Direction (i.e., read (1) or write (0), is the first bit in the ISS/ESR.
 */
#define ISS_DIRECTION_MASK UINT64_C(0x1)

/**
 * Gets the direction of the system register access, read (1) or write (0).
 */
#define GET_ISS_DIRECTION(esr) (ISS_DIRECTION_MASK & (esr))

/**
 * True if the ISS encoded in the esr indicates a read of the system register.
 */
#define ISS_IS_READ(esr) (ISS_DIRECTION_MASK & (esr))

/**
 * Returns the ISS encoding given the various instruction encoding parameters.
 */
#define GET_ISS_ENCODING(op0, op1, crn, crm, op2)          \
	((op0) << ISS_OP0_SHIFT | (op2) << ISS_OP2_SHIFT | \
	 (op1) << ISS_OP1_SHIFT | (crn) << ISS_CRN_SHIFT | \
	 (crm) << ISS_CRM_SHIFT)

#define PMCR_EL0_N_MASK UINT64_C(0xf800)
#define PMCR_EL0_N_SHIFT 11
#define GET_PMCR_EL0_N(pmcr) ((PMCR_EL0_N_MASK & (pmcr)) >> PMCR_EL0_N_SHIFT)

/*
 * Define various configurations bits for the Hypervisor Configuration Register,
 * HCR_EL2. See Arm Architecture Reference Manual, D13.2.46.
 */

/**
 * Trap ID group 5 (Armv8.5-MemTag related).
 */
#define HCR_EL2_TID5 (UINT64_C(0x1) << 58)

/**
 * Trap TLB maintenance instructions that operate on the Outer Shareable domain.
 */
#define HCR_EL2_TTLBOS (UINT64_C(0x1) << 55)

/**
 * Trap TLB maintenance instructions that operate on the Inner Shareable domain.
 */
#define HCR_EL2_TTLBIS (UINT64_C(0x1) << 54)

/**
 * Trap cache maintenance instructions that operate to the Point of Unification.
 */
#define HCR_EL2_TOCU (UINT64_C(0x1) << 52)

/**
 * Trap ICIALLUIS/IC IALLUIS cache maintenance instructions.
 */
#define HCR_EL2_TICAB (UINT64_C(0x1) << 52)

/**
 * Trap ID group 4.
 */
#define HCR_EL2_TID4 (UINT64_C(0x1) << 49)

/**
 * When set *disables* traps on Pointer Authentication related instruction
 * execution.
 */
#define HCR_EL2_API (UINT64_C(0x1) << 41)

/**
 * When set *disables* traps on access to Pointer Authentication's "key"
 * registers.
 */
#define HCR_EL2_APK (UINT64_C(0x1) << 40)

/**
 * Trap Error record accesses when RAS is implemented.
 */
#define HCR_EL2_TERR (UINT64_C(0x1) << 36)

/**
 * Trap LOR register accesses when LORegions is implemented.
 */
#define HCR_EL2_TLOR (UINT64_C(0x1) << 35)

/**
 * Stage 2 Instruction access cacheability disable.
 * When set, forces all stage 2 translations for instruction accesses to normal
 * memory to be non-cacheable.
 */
#define HCR_EL2_ID (UINT64_C(0x1) << 33)

/**
 * Stage 2 Data access cacheability disable.
 * When set, forces all stage 2 translations for data accesses to normal memory
 * to be non-cacheable.
 */
#define HCR_EL2_CD (UINT64_C(0x1) << 32)

/**
 * Execution state control for lower exception levels.
 * When set, the execution state for EL1 is AArch64.
 */
#define HCR_EL2_RW (UINT64_C(0x1) << 31)

/**
 * Trap reads of Virtual Memory controls.
 */
#define HCR_EL2_TRVM (UINT64_C(0x1) << 30)

/**
 * Trap writes of Virtual Memory controls.
 */
#define HCR_EL2_TVM (UINT64_C(0x1) << 26)

/**
 * Trap TLB maintenance instructions.
 */
#define HCR_EL2_TTLB (UINT64_C(0x1) << 25)

/**
 * Trap cache maintenance instructions.
 */
#define HCR_EL2_TPU (UINT64_C(0x1) << 24)

/**
 * Trap data or unified cache maintenance instructions.
 */
#define HCR_EL2_TPCP (UINT64_C(0x1) << 23)

/**
 * Trap data or unified cache maintenance instructions that operate by Set/Way.
 */
#define HCR_EL2_TSW (UINT64_C(0x1) << 22)

/**
 * Trap Auxiliary Control Registers.
 * When set, traps ACTLR_EL1 accesses to EL2.
 */
#define HCR_EL2_TACR (UINT64_C(0x1) << 21)

/**
 * Trap implementation defined functionality.
 * When set, traps EL1 accesses to implementation defined encodings to EL2.
 */
#define HCR_EL2_TIDCP (UINT64_C(0x1) << 20)

/**
 * Trap SMC instructions.
 * When set, traps EL1 execution of SMC instructions to EL2.
 */
#define HCR_EL2_TSC (UINT64_C(0x1) << 19)

/**
 * Trap ID group 3.
 */
#define HCR_EL2_TID3 (UINT64_C(0x1) << 18)

/**
 * Trap ID group 2.
 */
#define HCR_EL2_TID2 (UINT64_C(0x1) << 17)

/**
 * Trap ID group 1.
 */
#define HCR_EL2_TID1 (UINT64_C(0x1) << 16)

/**
 * Trap ID group 0.
 */
#define HCR_EL2_TID0 (UINT64_C(0x1) << 15)

/**
 * Traps EL0 and EL1 execution of Wait for Event (WFE) instructions to EL2.
 */
#define HCR_EL2_TWE (UINT64_C(0x1) << 14)

/**
 * Trap WFI instructions.
 * When set, traps EL0 and EL1 execution of WFI instructions to EL2.
 */
#define HCR_EL2_TWI (UINT64_C(0x1) << 13)

/**
 * Barrier Shareability upgrade (2 bits).
 * When set to 0b01, the minimum shareability domain to barrier instructions
 * is inner shareable.
 */
#define HCR_EL2_BSU_INNER_SHAREABLE (UINT64_C(0x1) << 10)

/**
 * Force Broadcast.
 * When set certain instructions related to invalidating the TLB are broadcast
 * within the Inner Shareable domain.
 */
#define HCR_EL2_FB (UINT64_C(0x1) << 9)

/**
 * Virtual IRQ Interrupt.
 * When set indicates that there is a virtual IRQ pending.
 */
#define HCR_EL2_VI (UINT64_C(0x1) << 7)

/**
 * Physical SError Routing.
 * When set, physical SError interrupts are taken to EL2, unless routed to EL3.
 */
#define HCR_EL2_AMO (UINT64_C(0x1) << 5)

/**
 * Physical IRQ Routing.
 * When set, physical IRQ interrupts are taken to EL2, unless routed to EL3.
 */
#define HCR_EL2_IMO (UINT64_C(0x1) << 4)

/**
 * Physical FIQ Routing.
 * When set, physical FIQ interrupts are taken to EL2, unless routed to EL3.
 */
#define HCR_EL2_FMO (UINT64_C(0x1) << 3)

/**
 * Protected Table Walk.
 * When set a translation table access made as part of a stage 1 translation
 * table walk is subject to a stage 2 translation. The memory access generates a
 * stage 2 permission fault.
 */
#define HCR_EL2_PTW (UINT64_C(0x1) << 2)

/**
 * Set/Way Invalidation Override.
 * Causes EL1 execution of the data cache invalidate by set/way instructions to
 * perform a data cache clean and invalidate by set/way.
 */
#define HCR_EL2_SWIO (UINT64_C(0x1) << 1)

/**
 * Virtualization enable.
 * When set EL1 and EL0 stage 2 address translation is enabled.
 */
#define HCR_EL2_VM (UINT64_C(0x1) << 0)

/**
 * Trap system register accesses to trace registers.
 * Traps accesses to ETM registers using the register interface. Does not trap
 * on accesses through the memory-mapped interface.
 */
#define CPTR_EL2_TTA (UINT64_C(0x1) << 28)

/*
 * Process State Bit definitions.
 *
 * These apply to the PSTATE, as well as registers that contain PSTATE fields,
 * e.g., SPSR_EL1.
 */

/**
 * Debug exception mask bit.
 */
#define PSR_D (UINT64_C(1) << 9)

/**
 * Asynchronous SError interrupt mask bit.
 */
#define PSR_A (UINT64_C(1) << 8)

/**
 * Asynchronous IRQ interrupt mask bit.
 */
#define PSR_I (UINT64_C(1) << 7)

/**
 * Asynchronous FIQ interrupt mask bit.
 */
#define PSR_F (UINT64_C(1) << 6)

/**
 * AArch32 State bit.
 */
#define PSR_ARCH_MODE_32 (UINT64_C(1) << 4)

/**
 * PE Mode bit mask.
 */
#define PSR_PE_MODE_MASK UINT64_C(0xf)

/**
 * PE Mode: EL0t.
 */
#define PSR_PE_MODE_EL0T UINT64_C(0x0)

/**
 * PE Mode: EL1h.
 */
#define PSR_PE_MODE_EL1H UINT64_C(0x5)

/*
 * Define configurations bits for the System Control Register (EL2), SCTLR_EL2.
 * See Arm Architecture Reference Manual, D13.2.106.
 */

/**
 * Reserved, RES1.
 */
#define SCTLR_EL2_B28 (UINT64_C(0x1) << 28)

/**
 * Exception entry is a context synchronization Event (Armv8.5-CSEH),
 * otherwise RES1.
 */
#define SCTLR_EL2_EIS (UINT64_C(0x1) << 22)

/**
 * Implicit Error Synchronization event enable (ARMv8.2-IESB).
 */
#define SCTLR_EL2_IESB (UINT64_C(0x1) << 21)

/**
 * Write permission implies XN (Execute-never).
 */
#define SCTLR_EL2_WXN (UINT64_C(0x1) << 19)

/**
 * Reserved, RES1.
 */
#define SCTLR_EL2_B18 (UINT64_C(0x1) << 18)

/**
 * Reserved, RES1.
 */
#define SCTLR_EL2_B16 (UINT64_C(0x1) << 16)

/**
 * Instruction access Cacheability control.
 */
#define SCTLR_EL2_I (UINT64_C(0x1) << 12)

/**
 * Exception exit is a context synchronization Event (Armv8.5-CSEH),
 * otherwise RES1.
 */
#define SCTLR_EL2_EOS (UINT64_C(0x1) << 11)

/**
 * Reserved, RES1.
 */
#define SCTLR_EL2_B4 (UINT64_C(0x3) << 4)

/**
 * SP Alignment check enable.
 */
#define SCTLR_EL2_SA (UINT64_C(0x1) << 3)

/**
 * Cacheability control, for data accesses.
 */
#define SCTLR_EL2_C (UINT64_C(0x1) << 2)

/**
 * Alignment check enable.
 */
#define SCTLR_EL2_A (UINT64_C(0x1) << 1)

/**
 * MMU enable for EL2 stage 1 address translation.
 */
#define SCTLR_EL2_M (UINT64_C(0x1) << 0)

uintreg_t get_hcr_el2_value(spci_vm_id_t vm_id);

uintreg_t get_mdcr_el2_value(void);

uintreg_t get_cptr_el2_value(void);

uintreg_t get_sctlr_el2_value(void);
