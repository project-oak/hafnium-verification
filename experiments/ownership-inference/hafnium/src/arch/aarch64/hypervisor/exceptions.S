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

#include "hf/arch/offsets.h"
#include "exception_macros.S"

/**
 * Saves the volatile registers into the register buffer of the current vCPU.
 */
.macro save_volatile_to_vcpu
	/*
	 * Save x18 since we're about to clobber it. We subtract 16 instead of
	 * 8 from the stack pointer to keep it 16-byte aligned.
	 */
	str x18, [sp, #-16]!

	/* Get the current vCPU. */
	mrs x18, tpidr_el2
	stp x0, x1, [x18, #VCPU_REGS + 8 * 0]
	stp x2, x3, [x18, #VCPU_REGS + 8 * 2]
	stp x4, x5, [x18, #VCPU_REGS + 8 * 4]
	stp x6, x7, [x18, #VCPU_REGS + 8 * 6]
	stp x8, x9, [x18, #VCPU_REGS + 8 * 8]
	stp x10, x11, [x18, #VCPU_REGS + 8 * 10]
	stp x12, x13, [x18, #VCPU_REGS + 8 * 12]
	stp x14, x15, [x18, #VCPU_REGS + 8 * 14]
	stp x16, x17, [x18, #VCPU_REGS + 8 * 16]
	stp x29, x30, [x18, #VCPU_REGS + 8 * 29]

	/* x18 was saved on the stack, so we move it to vCPU regs buffer. */
	ldr x0, [sp], #16
	str x0, [x18, #VCPU_REGS + 8 * 18]

	/* Save return address & mode. */
	mrs x1, elr_el2
	mrs x2, spsr_el2
	stp x1, x2, [x18, #VCPU_REGS + 8 * 31]
.endm

/**
 * This is a generic handler for exceptions taken at a lower EL. It saves the
 * volatile registers to the current vCPU and calls the C handler, which can
 * select one of two paths: (a) restore volatile registers and return, or
 * (b) switch to a different vCPU. In the latter case, the handler needs to save
 * all non-volatile registers (they haven't been saved yet), then restore all
 * registers from the new vCPU.
 */
.macro lower_exception handler:req
	save_volatile_to_vcpu

	/* Call C handler. */
	bl \handler

	/* Switch vCPU if requested by handler. */
	cbnz x0, vcpu_switch

	/* vCPU is not changing. */
	mrs x0, tpidr_el2
	b vcpu_restore_volatile_and_run
.endm

/**
 * This is the handler for a sync exception taken at a lower EL.
 */
.macro lower_sync_exception
	save_volatile_to_vcpu

	/* Extract the exception class (EC) from exception syndrome register. */
	mrs x18, esr_el2
	lsr x18, x18, #26

	/* Take the system register path for EC 0x18. */
	sub x18, x18, #0x18
	cbz x18, system_register_access

	/* Read syndrome register and call C handler. */
	mrs x0, esr_el2
	bl sync_lower_exception

	/* Switch vCPU if requested by handler. */
	cbnz x0, vcpu_switch

	/* vCPU is not changing. */
	mrs x0, tpidr_el2
	b vcpu_restore_volatile_and_run
.endm

/**
 * The following is the exception table. A pointer to it will be stored in
 * register vbar_el2.
 */
.section .text.vector_table_el2, "ax"
.global vector_table_el2
.balign 0x800
vector_table_el2:
sync_cur_sp0:
	noreturn_current_exception_sp0 el2 sync_current_exception_noreturn

.balign 0x80
irq_cur_sp0:
	noreturn_current_exception_sp0 el2 irq_current_exception_noreturn

.balign 0x80
fiq_cur_sp0:
	noreturn_current_exception_sp0 el2 fiq_current_exception_noreturn

.balign 0x80
serr_cur_sp0:
	noreturn_current_exception_sp0 el2 serr_current_exception_noreturn

.balign 0x80
sync_cur_spx:
	noreturn_current_exception_spx el2 sync_current_exception_noreturn

.balign 0x80
irq_cur_spx:
	noreturn_current_exception_spx el2 irq_current_exception_noreturn

.balign 0x80
fiq_cur_spx:
	noreturn_current_exception_spx el2 fiq_current_exception_noreturn

.balign 0x80
serr_cur_spx:
	noreturn_current_exception_spx el2 serr_current_exception_noreturn

.balign 0x80
sync_lower_64:
	lower_sync_exception

.balign 0x80
irq_lower_64:
	lower_exception irq_lower

.balign 0x80
fiq_lower_64:
	lower_exception fiq_lower

.balign 0x80
serr_lower_64:
	lower_exception serr_lower

.balign 0x80
sync_lower_32:
	lower_sync_exception

.balign 0x80
irq_lower_32:
	lower_exception irq_lower

.balign 0x80
fiq_lower_32:
	lower_exception fiq_lower

.balign 0x80
serr_lower_32:
	lower_exception serr_lower

.balign 0x40

/**
 * Handle accesses to system registers (EC=0x18) and return to original caller.
 */
system_register_access:
	/*
	 * Non-volatile registers are (conservatively) saved because the handler
	 * can clobber non-volatile registers that are used by the msr/mrs,
	 * which results in the wrong value being read or written.
	 */
	/* Get the current vCPU. */
	mrs x18, tpidr_el2
	stp x19, x20, [x18, #VCPU_REGS + 8 * 19]
	stp x21, x22, [x18, #VCPU_REGS + 8 * 21]
	stp x23, x24, [x18, #VCPU_REGS + 8 * 23]
	stp x25, x26, [x18, #VCPU_REGS + 8 * 25]
	stp x27, x28, [x18, #VCPU_REGS + 8 * 27]

	/* Read syndrome register and call C handler. */
	mrs x0, esr_el2
	bl handle_system_register_access

	/* Continue running the same vCPU. */
	mrs x0, tpidr_el2
	b vcpu_restore_nonvolatile_and_run

/**
 * Switch to a new vCPU.
 *
 * All volatile registers from the old vCPU have already been saved. We need
 * to save only non-volatile ones from the old vCPU, and restore all from the
 * new one.
 *
 * x0 is a pointer to the new vCPU.
 */
vcpu_switch:
	/* Save non-volatile registers. */
	mrs x1, tpidr_el2
	stp x19, x20, [x1, #VCPU_REGS + 8 * 19]
	stp x21, x22, [x1, #VCPU_REGS + 8 * 21]
	stp x23, x24, [x1, #VCPU_REGS + 8 * 23]
	stp x25, x26, [x1, #VCPU_REGS + 8 * 25]
	stp x27, x28, [x1, #VCPU_REGS + 8 * 27]

	/* Save lazy state. */
	/* Use x28 as the base */
	add x28, x1, #VCPU_LAZY

	mrs x24, vmpidr_el2
	mrs x25, csselr_el1
	stp x24, x25, [x28], #16

	mrs x2, sctlr_el1
	mrs x3, actlr_el1
	stp x2, x3, [x28], #16

	mrs x4, cpacr_el1
	mrs x5, ttbr0_el1
	stp x4, x5, [x28], #16

	mrs x6, ttbr1_el1
	mrs x7, tcr_el1
	stp x6, x7, [x28], #16

	mrs x8, esr_el1
	mrs x9, afsr0_el1
	stp x8, x9, [x28], #16

	mrs x10, afsr1_el1
	mrs x11, far_el1
	stp x10, x11, [x28], #16

	mrs x12, mair_el1
	mrs x13, vbar_el1
	stp x12, x13, [x28], #16

	mrs x14, contextidr_el1
	mrs x15, tpidr_el0
	stp x14, x15, [x28], #16

	mrs x16, tpidrro_el0
	mrs x17, tpidr_el1
	stp x16, x17, [x28], #16

	mrs x18, amair_el1
	mrs x19, cntkctl_el1
	stp x18, x19, [x28], #16

	mrs x20, sp_el0
	mrs x21, sp_el1
	stp x20, x21, [x28], #16

	mrs x22, elr_el1
	mrs x23, spsr_el1
	stp x22, x23, [x28], #16

	mrs x24, par_el1
	mrs x25, hcr_el2
	stp x24, x25, [x28], #16

	mrs x26, cnthctl_el2
	mrs x27, vttbr_el2
	stp x26, x27, [x28], #16

	mrs x4, mdcr_el2
	mrs x5, mdscr_el1
	stp x4, x5, [x28], #16

	mrs x6, pmccfiltr_el0
	mrs x7, pmcr_el0
	stp x6, x7, [x28], #16

	mrs x8, pmcntenset_el0
	mrs x9, pmintenset_el1
	stp x8, x9, [x28], #16

	/* Save GIC registers. */
#if GIC_VERSION == 3 || GIC_VERSION == 4
	/* Offset is too large, so start from a new base. */
	add x2, x1, #VCPU_GIC

	mrs x3, ich_hcr_el2
	mrs x4, icc_sre_el2
	stp x3, x4, [x2, #16 * 0]
#endif

	/* Save floating point registers. */
	/* Use x28 as the base. */
	add x28, x1, #VCPU_FREGS
	stp q0, q1, [x28], #32
	stp q2, q3, [x28], #32
	stp q4, q5, [x28], #32
	stp q6, q7, [x28], #32
	stp q8, q9, [x28], #32
	stp q10, q11, [x28], #32
	stp q12, q13, [x28], #32
	stp q14, q15, [x28], #32
	stp q16, q17, [x28], #32
	stp q18, q19, [x28], #32
	stp q20, q21, [x28], #32
	stp q22, q23, [x28], #32
	stp q24, q25, [x28], #32
	stp q26, q27, [x28], #32
	stp q28, q29, [x28], #32
	stp q30, q31, [x28], #32
	mrs x3, fpsr
	mrs x4, fpcr
	stp x3, x4, [x28], #32

	/* Save new vCPU pointer in non-volatile register. */
	mov x19, x0

	/*
	 * Save peripheral registers, and inform the arch-independent sections
	 * that registers have been saved.
	 */
	mov x0, x1
	bl complete_saving_state
	mov x0, x19

	/* Intentional fallthrough. */
.global vcpu_restore_all_and_run
vcpu_restore_all_and_run:
	/* Update pointer to current vCPU. */
	msr tpidr_el2, x0

	/* Restore peripheral registers. */
	mov x19, x0
	bl begin_restoring_state
	mov x0, x19

	/*
	 * Restore floating point registers.
	 *
	 * Offset is too large, so start from a new base.
	 */
	add x2, x0, #VCPU_FREGS
	ldp q0, q1, [x2, #32 * 0]
	ldp q2, q3, [x2, #32 * 1]
	ldp q4, q5, [x2, #32 * 2]
	ldp q6, q7, [x2, #32 * 3]
	ldp q8, q9, [x2, #32 * 4]
	ldp q10, q11, [x2, #32 * 5]
	ldp q12, q13, [x2, #32 * 6]
	ldp q14, q15, [x2, #32 * 7]
	ldp q16, q17, [x2, #32 * 8]
	ldp q18, q19, [x2, #32 * 9]
	ldp q20, q21, [x2, #32 * 10]
	ldp q22, q23, [x2, #32 * 11]
	ldp q24, q25, [x2, #32 * 12]
	ldp q26, q27, [x2, #32 * 13]
	ldp q28, q29, [x2, #32 * 14]
	/* Offset becomes too large, so move the base. */
	ldp q30, q31, [x2, #32 * 15]!
	ldp x3, x4, [x2, #32 * 1]
	msr fpsr, x3

	/*
	 * Only restore FPCR if changed, to avoid expensive
	 * self-synchronising operation where possible.
	 */
	mrs x5, fpcr
	cmp x5, x4
	b.eq vcpu_restore_lazy_and_run
	msr fpcr, x4
	/* Intentional fallthrough. */

vcpu_restore_lazy_and_run:
	/* Restore lazy registers. */
	/* Use x28 as the base. */
	add x28, x0, #VCPU_LAZY

	ldp x24, x25, [x28], #16
	msr vmpidr_el2, x24
	msr csselr_el1, x25

	ldp x2, x3, [x28], #16
	msr sctlr_el1, x2
	msr actlr_el1, x3

	ldp x4, x5, [x28], #16
	msr cpacr_el1, x4
	msr ttbr0_el1, x5

	ldp x6, x7, [x28], #16
	msr ttbr1_el1, x6
	msr tcr_el1, x7

	ldp x8, x9, [x28], #16
	msr esr_el1, x8
	msr afsr0_el1, x9

	ldp x10, x11, [x28], #16
	msr afsr1_el1, x10
	msr far_el1, x11

	ldp x12, x13, [x28], #16
	msr mair_el1, x12
	msr vbar_el1, x13

	ldp x14, x15, [x28], #16
	msr contextidr_el1, x14
	msr tpidr_el0, x15

	ldp x16, x17, [x28], #16
	msr tpidrro_el0, x16
	msr tpidr_el1, x17

	ldp x18, x19, [x28], #16
	msr amair_el1, x18
	msr cntkctl_el1, x19

	ldp x20, x21, [x28], #16
	msr sp_el0, x20
	msr sp_el1, x21

	ldp x22, x23, [x28], #16
	msr elr_el1, x22
	msr spsr_el1, x23

	ldp x24, x25, [x28], #16
	msr par_el1, x24
	msr hcr_el2, x25

	ldp x26, x27, [x28], #16
	msr cnthctl_el2, x26
	msr vttbr_el2, x27

	ldp x4, x5, [x28], #16
	msr mdcr_el2, x4
	msr mdscr_el1, x5

	ldp x6, x7, [x28], #16
	msr pmccfiltr_el0, x6
	msr pmcr_el0, x7

	ldp x8, x9, [x28], #16
	/*
	 * NOTE: Writing 0s to pmcntenset_el0's bits do not alter their values.
	 * To reset them, clear the register by writing to pmcntenclr_el0.
	 */
	mov x27, #0xffffffff
	msr pmcntenclr_el0, x27
	msr pmcntenset_el0, x8

	/*
	 * NOTE: Writing 0s to pmintenset_el1's bits do not alter their values.
	 * To reset them, clear the register by writing to pmintenclr_el1.
	 */
	msr pmintenclr_el1, x27
	msr pmintenset_el1, x9

	/* Restore GIC registers. */
#if GIC_VERSION == 3 || GIC_VERSION == 4
	/* Offset is too large, so start from a new base. */
	add x2, x0, #VCPU_GIC

	ldp x3, x4, [x2, #16 * 0]
	msr ich_hcr_el2, x3
	msr icc_sre_el2, x4
#endif

	/*
	 * If a different vCPU is being run on this physical CPU to the last one
	 * which was run for this VM, invalidate the TLB. This must be called
	 * after vttbr_el2 has been updated, so that we have the page table and
	 * VMID of the vCPU to which we are switching.
	 */
	mov x19, x0
	bl maybe_invalidate_tlb
	mov x0, x19

	/* Intentional fallthrough. */

vcpu_restore_nonvolatile_and_run:
	/* Restore non-volatile registers. */
	ldp x19, x20, [x0, #VCPU_REGS + 8 * 19]
	ldp x21, x22, [x0, #VCPU_REGS + 8 * 21]
	ldp x23, x24, [x0, #VCPU_REGS + 8 * 23]
	ldp x25, x26, [x0, #VCPU_REGS + 8 * 25]
	ldp x27, x28, [x0, #VCPU_REGS + 8 * 27]

	/* Intentional fallthrough. */
/**
 * Restore volatile registers and run the given vCPU.
 *
 * x0 is a pointer to the target vCPU.
 */
vcpu_restore_volatile_and_run:
	ldp x4, x5, [x0, #VCPU_REGS + 8 * 4]
	ldp x6, x7, [x0, #VCPU_REGS + 8 * 6]
	ldp x8, x9, [x0, #VCPU_REGS + 8 * 8]
	ldp x10, x11, [x0, #VCPU_REGS + 8 * 10]
	ldp x12, x13, [x0, #VCPU_REGS + 8 * 12]
	ldp x14, x15, [x0, #VCPU_REGS + 8 * 14]
	ldp x16, x17, [x0, #VCPU_REGS + 8 * 16]
	ldr x18, [x0, #VCPU_REGS + 8 * 18]
	ldp x29, x30, [x0, #VCPU_REGS + 8 * 29]

	/* Restore return address & mode. */
	ldp x1, x2, [x0, #VCPU_REGS + 8 * 31]
	msr elr_el2, x1
	msr spsr_el2, x2

	/* Restore x0..x3, which we have used as scratch before. */
	ldp x2, x3, [x0, #VCPU_REGS + 8 * 2]
	ldp x0, x1, [x0, #VCPU_REGS + 8 * 0]
	eret_with_sb

.balign 0x40
/**
 * Restore volatile registers from stack and return to original caller.
 */
restore_from_stack_and_return:
	restore_volatile_from_stack el2
	eret_with_sb
