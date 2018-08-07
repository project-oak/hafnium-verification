.section .init.image, "ax"

.global image_entry
image_entry:
	/* Prepare the stack. */
	adr x0, kstack + 4096
	mov sp, x0

	/* Call into C code. */
	bl kmain

	/* If the VM returns, shutdown the system. */
	bl shutdown

	/* Loop forever waiting for interrupts. */
0:	wfi
	b 0b
