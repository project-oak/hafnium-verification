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

/**
 * From Linux commit 679db70801da9fda91d26caf13bf5b5ccc74e8e8:
 * "Some CPUs can speculate past an ERET instruction and potentially perform
 * speculative accesses to memory before processing the exception return.
 * Since the register state is often controlled by a lower privilege level
 * at the point of an ERET, this could potentially be used as part of a
 * side-channel attack."
 *
 * This macro emits a speculation barrier after the ERET to prevent the CPU
 * from speculating past the exception return.
 *
 * ARMv8.5 introduces a dedicated SB speculative barrier instruction.
 * Use a DSB/ISB pair on older platforms.
 */
.macro eret_with_sb
	eret
	dsb	nsh
	isb
.endm

/**
 * Saves the volatile registers onto the stack. This currently takes 14
 * instructions, so it can be used in exception handlers with 18 instructions
 * left, 2 of which in the same cache line (assuming a 16-byte cache line).
 *
 * On return, x0 and x1 are initialised to elr_el2 and spsr_el2 respectively,
 * which can be used as the first and second arguments of a subsequent call.
 */
.macro save_volatile_to_stack elx:req
	/* Reserve stack space and save registers x0-x18, x29 & x30. */
	stp x0, x1, [sp, #-(8 * 24)]!
	stp x2, x3, [sp, #8 * 2]
	stp x4, x5, [sp, #8 * 4]
	stp x6, x7, [sp, #8 * 6]
	stp x8, x9, [sp, #8 * 8]
	stp x10, x11, [sp, #8 * 10]
	stp x12, x13, [sp, #8 * 12]
	stp x14, x15, [sp, #8 * 14]
	stp x16, x17, [sp, #8 * 16]
	str x18, [sp, #8 * 18]
	stp x29, x30, [sp, #8 * 20]

	/*
	 * Save elr_elx & spsr_elx. This such that we can take nested exception
	 * and still be able to unwind.
	 */
	mrs x0, elr_\elx
	mrs x1, spsr_\elx
	stp x0, x1, [sp, #8 * 22]
.endm

/**
 * Restores the volatile registers from the stack. This currently takes 14
 * instructions, so it can be used in exception handlers while still leaving 18
 * instructions left; if paired with save_volatile_to_stack, there are 4
 * instructions to spare.
 */
.macro restore_volatile_from_stack elx:req
	/* Restore registers x2-x18, x29 & x30. */
	ldp x2, x3, [sp, #8 * 2]
	ldp x4, x5, [sp, #8 * 4]
	ldp x6, x7, [sp, #8 * 6]
	ldp x8, x9, [sp, #8 * 8]
	ldp x10, x11, [sp, #8 * 10]
	ldp x12, x13, [sp, #8 * 12]
	ldp x14, x15, [sp, #8 * 14]
	ldp x16, x17, [sp, #8 * 16]
	ldr x18, [sp, #8 * 18]
	ldp x29, x30, [sp, #8 * 20]

	/* Restore registers elr_elx & spsr_elx, using x0 & x1 as scratch. */
	ldp x0, x1, [sp, #8 * 22]
	msr elr_\elx, x0
	msr spsr_\elx, x1

	/* Restore x0 & x1, and release stack space. */
	ldp x0, x1, [sp], #8 * 24
.endm

/**
 * This is a generic handler for exceptions taken at the current EL while using
 * SP0. It behaves similarly to the SPx case by first switching to SPx, doing
 * the work, then switching back to SP0 before returning.
 *
 * Switching to SPx and calling the C handler takes 16 instructions, so it's not
 * possible to add a branch to a common exit path without going into the next
 * cache line (assuming 16-byte cache lines). Additionally, to restore and
 * return we need an additional 16 instructions, so we could implement the whole
 * handler within the allotted 32 instructions. However, since we want to emit
 * a speculation barrier after each ERET, we are forced to move the ERET to
 * a shared exit path.
 */
.macro current_exception_sp0 elx:req handler:req eret_label:req
	msr spsel, #1
	save_volatile_to_stack \elx
	bl \handler
	restore_volatile_from_stack \elx
	msr spsel, #0
	b \eret_label
.endm

/**
 * Variant of current_exception_sp0 which assumes the handler never returns.
 */
.macro noreturn_current_exception_sp0 elx:req handler:req
	msr spsel, #1
	save_volatile_to_stack \elx
	b \handler
.endm

/**
 * This is a generic handler for exceptions taken at the current EL while using
 * SPx. It saves volatile registers, calls the C handler, restores volatile
 * registers, then returns.
 *
 * Saving state and jumping to C handler takes 15 instructions. We add an extra
 * branch to a common exit path. So each handler takes up one unique cache line
 * and one shared cache line (assuming 16-byte cache lines).
 */
.macro current_exception_spx elx:req handler:req
	save_volatile_to_stack \elx
	bl \handler
	b restore_from_stack_and_return
.endm

/**
 * Variant of current_exception_spx which assumes the handler never returns.
 */
.macro noreturn_current_exception_spx elx:req handler:req
	save_volatile_to_stack \elx
	b \handler
.endm
