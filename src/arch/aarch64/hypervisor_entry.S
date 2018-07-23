#include "offsets.h"

.section .init.image, "ax"

.global image_entry
image_entry:
	/* Save the FDT to a global variable. */
	adrp x30, fdt_addr
	add x30, x30, :lo12:fdt_addr
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
