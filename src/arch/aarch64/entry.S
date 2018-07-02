#include "offsets.h"

#define PECOFF_FILE_ALIGNMENT 0x200

.section .init.entry, "ax"

.global entry
entry:

	add x13, x18, #0x16
	b 0f
	.quad 4096        /* text_offset */
	.quad file_size   /* image_size */
	.quad 0           /* flags */
	.quad 0           /* res2 */
	.quad 0           /* res3 */
	.quad 0           /* res4 */
	.word 0x644d5241  /* magic */
	.word 0

	/*
	 * Calculate the difference between the actual load address and the
	 * preferred one. We'll use this to relocate.
	 */
0:	adrp x25, entry
	add x25, x25, :lo12:entry

	ldr w29, =_orig_base

	sub x25, x25, x29

	/* Find where the relocations begin and end. */
	adrp x29, rela_begin
	add x29, x29, :lo12:rela_begin

	adrp x30, rela_end
	add x30, x30, :lo12:rela_end

	/* Iterate over all relocations. */
1:	cmp x29, x30
	b.eq 2f

	ldp x26, x27, [x29], #16
	ldr x28, [x29], #8

	cmp w27, #1027 /* R_AARCH64_RELATIVE */
#	b.ne 1b
	b.ne .

	add x28, x28, x25
	str x28, [x26, x25]
	b 1b

	/* Zero out the bss section. */
2:	adrp x29, bss_begin
	add x29, x29, :lo12:bss_begin

	adrp x30, bss_end
	add x30, x30, :lo12:bss_end

3:	cmp x29, x30
	b.hs 4f

	stp xzr, xzr, [x29], #16
	b 3b

4:	/* Save the FDT to a global variable. */
	adrp x30, fdt
	add x30, x30, :lo12:fdt
	str x0, [x30]

	/* Get pointer to first cpu. */
	adrp x0, cpus
	add x0, x0, :lo12:cpus


.globl cpu_entry
cpu_entry:
	/* Disable interrupts. */
	msr DAIFSet, #0xf

	/* Save pointer to CPU struct for later reference. */
	msr tpidr_el2, x0

	/* Use SPx (instead of SP0). */
	msr spsel, #1

	/* Prepare the stack. */
	ldr x30, [x0, #CPU_STACK_BOTTOM]
	mov sp, x30

	/* Configure exception handlers. */
	adrp x30, vector_table_el2
	add x30, x30, :lo12:vector_table_el2
	msr vbar_el2, x30

	/* Call into C code. */
	bl cpu_main

	/* Run the vcpu returned by cpu_main. */
	b vcpu_restore_all_and_run

	/* Loop forever waiting for interrupts. */
5:	wfi
	b 5b

/* TODO: Move this elsewhere. */
.globl smc
smc:
	SMC #0
	ret
