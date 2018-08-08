.section .text.smc, "ax"
.globl smc
smc:
	smc #0
	ret
