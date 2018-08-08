.section .init.image_entry, "ax"
.global image_entry
image_entry:
	/* Save the FDT to a global variable. */
	adrp x30, fdt_addr
	add x30, x30, :lo12:fdt_addr
	str x0, [x30]

	/* Get pointer to first cpu. */
	adrp x0, cpus
	add x0, x0, :lo12:cpus

	b cpu_entry

