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

#include "offsets.h"

.section .text.vector_table_el2, "ax"
.global vector_table_el2
.balign 0x800
vector_table_el2:
sync_cur_sp0:
	b .

.balign 0x80
irq_cur_sp0:
	b irq_current

.balign 0x80
fiq_cur_sp0:
	b .

.balign 0x80
serr_cur_sp0:
	b .

.balign 0x80
sync_cur_spx:
	mrs x0, esr_el2
	mrs x1, elr_el2
	b sync_current_exception

.balign 0x80
irq_cur_spx:
	b irq_current

.balign 0x80
fiq_cur_spx:
	b .

.balign 0x80
serr_cur_spx:
	b .

.balign 0x80
sync_lower_64:

	/*
	 * Save x18 since we're about to clobber it. We subtract 16 instead of
	 * 8 from the stack pointer to keep it 16-byte aligned.
	 */
	str x18, [sp, #-16]!

	/* Extract the exception class (EC) from exception syndrome register. */
	mrs x18, esr_el2
	lsr x18, x18, #26

	/* Take the slow path if exception is not due to an HVC instruction. */
	sub x18, x18, #0x16
	cbnz x18, slow_sync_lower_64

	/*
	 * Save x29 and x30, which are not saved by the callee, then jump to
	 * HVC handler.
	 */
	stp x29, x30, [sp, #-16]!
	bl hvc_handler
	ldp x29, x30, [sp], #16
	cbnz x1, sync_lower_64_switch

	/* Zero out all volatile registers (except x0) and return. */
	stp xzr, xzr, [sp, #-16]!
	ldp x1, x2, [sp]
	ldp x3, x4, [sp]
	ldp x5, x6, [sp]
	ldp x7, x8, [sp]
	ldp x9, x10, [sp]
	ldp x11, x12, [sp]
	ldp x13, x14, [sp]
	ldp x15, x16, [sp], #16
	mov x17, xzr

	/* Restore x18, which was saved on the stack. */
	ldr x18, [sp], #16
	eret

.balign 0x80
irq_lower_64:

	/* Save x0 since we're about to clobber it. */
	str x0, [sp, #-8]!

	/* Get the current vcpu. */
	mrs x0, tpidr_el2

	/* Save volatile registers. */
	add x0, x0, #VCPU_REGS
	stp x2, x3, [x0, #8 * 2]
	stp x4, x5, [x0, #8 * 4]
	stp x6, x7, [x0, #8 * 6]
	stp x8, x9, [x0, #8 * 8]
	stp x10, x11, [x0, #8 * 10]
	stp x12, x13, [x0, #8 * 12]
	stp x14, x15, [x0, #8 * 14]
	stp x16, x17, [x0, #8 * 16]
	str x18, [x0, #8 * 18]
	stp x29, x30, [x0, #8 * 29]

	ldr x2, [sp], #8
	stp x2, x1, [x0, #8 * 0]

	/* Save return address & mode. */
	mrs x1, elr_el2
	mrs x2, spsr_el2
	stp x1, x2, [x0, #8 * 31]

	/* Call C handler. */
	bl irq_lower

	mrs x1, tpidr_el2
	cbnz x0, vcpu_switch

	/* vcpu is not changing. */
	add x0, x1, #VCPU_REGS
	b vcpu_restore_volatile_and_run

.balign 0x80
fiq_lower_64:
	b .

.balign 0x80
serr_lower_64:
	b .

.balign 0x80
sync_lower_32:
	b .

.balign 0x80
irq_lower_32:
	b .

.balign 0x80
fiq_lower_32:
	b .

.balign 0x80
serr_lower_32:
	b .

slow_sync_lower_64:
	/* Get the current vcpu. */
	mrs x18, tpidr_el2

	/* Save volatile registers. */
	add x18, x18, #VCPU_REGS
	stp x0, x1, [x18, #8 * 0]
	stp x2, x3, [x18, #8 * 2]
	stp x4, x5, [x18, #8 * 4]
	stp x6, x7, [x18, #8 * 6]
	stp x8, x9, [x18, #8 * 8]
	stp x10, x11, [x18, #8 * 10]
	stp x12, x13, [x18, #8 * 12]
	stp x14, x15, [x18, #8 * 14]
	stp x16, x17, [x18, #8 * 16]
	stp x29, x30, [x18, #8 * 29]

	/* x18 was saved on the stack, so we move it to vcpu regs buffer. */
	ldr x0, [sp], #16
	str x0, [x18, #8 * 18]

	/* Save return address & mode. */
	mrs x1, elr_el2
	mrs x2, spsr_el2
	stp x1, x2, [x18, #8 * 31]

	/* Read syndrome register and call C handler. */
	mrs x0, esr_el2
	bl sync_lower_exception

	/* Switch to the vcpu returned by sync_lower_exception. */
	mrs x1, tpidr_el2
	cbnz x0, vcpu_switch

	/* vcpu is not changing. */
	add x0, x1, #VCPU_REGS
	b vcpu_restore_volatile_and_run

sync_lower_64_switch:
	/* We'll have to switch, so save volatile state before doing so. */
	mrs x18, tpidr_el2

	/* Store zeroes in volatile register storage, except x0. */
	add x18, x18, #VCPU_REGS
	stp x0, xzr, [x18, #8 * 0]
	stp xzr, xzr, [x18, #8 * 2]
	stp xzr, xzr, [x18, #8 * 4]
	stp xzr, xzr, [x18, #8 * 6]
	stp xzr, xzr, [x18, #8 * 8]
	stp xzr, xzr, [x18, #8 * 10]
	stp xzr, xzr, [x18, #8 * 12]
	stp xzr, xzr, [x18, #8 * 14]
	stp xzr, xzr, [x18, #8 * 16]
	stp x29, x30, [x18, #8 * 29]

	/* x18 was saved on the stack, so we move it to vcpu regs buffer. */
	ldr x2, [sp], #16
	str x2, [x18, #8 * 18]

	/* Save return address & mode. */
	mrs x2, elr_el2
	mrs x3, spsr_el2
	stp x2, x3, [x18, #8 * 31]

	/* Save lazy state, then switch to new vcpu. */
	mov x0, x1
	sub x1, x18, #VCPU_REGS

	/* Intentional fallthrough. */
/**
 * Switch to a new vcpu.
 *
 * All volatile registers from the old vcpu have already been saved. We need
 * to save only non-volatile ones from the old vcpu, and restore all from the
 * new one.
 *
 * x0 is a pointer to the new vcpu.
 * x1 is a pointer to the old vcpu.
 */
vcpu_switch:
	/* Save non-volatile registers. */
	add x1, x1, #VCPU_REGS
	stp x19, x20, [x1, #8 * 19]
	stp x21, x22, [x1, #8 * 21]
	stp x23, x24, [x1, #8 * 23]
	stp x25, x26, [x1, #8 * 25]
	stp x27, x28, [x1, #8 * 27]

	/* Save lazy state. */
	add x1, x1, #(VCPU_LAZY - VCPU_REGS)

	mrs x24, vmpidr_el2
	mrs x25, csselr_el1
	stp x24, x25, [x1, #16 * 0]

	mrs x2, sctlr_el1
	mrs x3, actlr_el1
	stp x2, x3, [x1, #16 * 1]

	mrs x4, cpacr_el1
	mrs x5, ttbr0_el1
	stp x4, x5, [x1, #16 * 2]

	mrs x6, ttbr1_el1
	mrs x7, tcr_el1
	stp x6, x7, [x1, #16 * 3]

	mrs x8, esr_el1
	mrs x9, afsr0_el1
	stp x8, x9, [x1, #16 * 4]

	mrs x10, afsr1_el1
	mrs x11, far_el1
	stp x10, x11, [x1, #16 * 5]

	mrs x12, mair_el1
	mrs x13, vbar_el1
	stp x12, x13, [x1, #16 * 6]

	mrs x14, contextidr_el1
	mrs x15, tpidr_el0
	stp x14, x15, [x1, #16 * 7]

	mrs x16, tpidrro_el0
	mrs x17, tpidr_el1
	stp x16, x17, [x1, #16 * 8]

	mrs x18, amair_el1
	mrs x19, cntkctl_el1
	stp x18, x19, [x1, #16 * 9]

	mrs x20, sp_el0
	mrs x21, sp_el1
	stp x20, x21, [x1, #16 * 10]

	mrs x22, par_el1
	mrs x23, hcr_el2
	stp x22, x23, [x1, #16 * 11]

	mrs x24, cptr_el2
	mrs x25, cnthctl_el2
	stp x24, x25, [x1, #16 * 12]

	mrs x26, vttbr_el2
	str x26, [x1, #16 * 13]

	/* Intentional fallthrough. */

.globl vcpu_restore_all_and_run
vcpu_restore_all_and_run:
	/* Update pointer to current vcpu. */
	msr tpidr_el2, x0

	/* Get a pointer to the lazy registers. */
	add x0, x0, #VCPU_LAZY

	ldp x24, x25, [x0, #16 * 0]
	msr vmpidr_el2, x24
	msr csselr_el1, x25

	ldp x2, x3, [x0, #16 * 1]
	msr sctlr_el1, x2
	msr actlr_el1, x3

	ldp x4, x5, [x0, #16 * 2]
	msr cpacr_el1, x4
	msr ttbr0_el1, x5

	ldp x6, x7, [x0, #16 * 3]
	msr ttbr1_el1, x6
	msr tcr_el1, x7

	ldp x8, x9, [x0, #16 * 4]
	msr esr_el1, x8
	msr afsr0_el1, x9

	ldp x10, x11, [x0, #16 * 5]
	msr afsr1_el1, x10
	msr far_el1, x11

	ldp x12, x13, [x0, #16 * 6]
	msr mair_el1, x12
	msr vbar_el1, x13

	ldp x14, x15, [x0, #16 * 7]
	msr contextidr_el1, x14
	msr tpidr_el0, x15

	ldp x16, x17, [x0, #16 * 8]
	msr tpidrro_el0, x16
	msr tpidr_el1, x17

	ldp x18, x19, [x0, #16 * 9]
	msr amair_el1, x18
	msr cntkctl_el1, x19

	ldp x20, x21, [x0, #16 * 10]
	msr sp_el0, x20
	msr sp_el1, x21

	ldp x22, x23, [x0, #16 * 11]
	msr par_el1, x22
	msr hcr_el2, x23

	ldp x24, x25, [x0, #16 * 12]
	msr cptr_el2, x22
	msr cnthctl_el2, x23

	ldr x26, [x0, #16 * 13]
	msr vttbr_el2, x26

	/* Restore non-volatile registers. */
	add x0, x0, #(VCPU_REGS - VCPU_LAZY)

	ldp x19, x20, [x0, #8 * 19]
	ldp x21, x22, [x0, #8 * 21]
	ldp x23, x24, [x0, #8 * 23]
	ldp x25, x26, [x0, #8 * 25]
	ldp x27, x28, [x0, #8 * 27]

	/* Intentional fallthrough. */

/**
 * Restore volatile registers and run the given vcpu.
 *
 * x0 is a pointer to the volatile registers of the target vcpu.
 */
vcpu_restore_volatile_and_run:
	ldp x4, x5, [x0, #8 * 4]
	ldp x6, x7, [x0, #8 * 6]
	ldp x8, x9, [x0, #8 * 8]
	ldp x10, x11, [x0, #8 * 10]
	ldp x12, x13, [x0, #8 * 12]
	ldp x14, x15, [x0, #8 * 14]
	ldp x16, x17, [x0, #8 * 16]
	ldr x18, [x0, #8 * 18]
	ldp x29, x30, [x0, #8 * 29]

	/* Restore return address & mode. */
	ldp x1, x2, [x0, #8 * 31]
	msr elr_el2, x1
	msr spsr_el2, x2

	/* Restore x0..x3, which we have used as scratch before. */
	ldp x2, x3, [x0, #8 * 2]
	ldp x0, x1, [x0, #8 * 0]
	eret
