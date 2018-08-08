.section .text.hf_call, "ax"
.global hf_call
hf_call:
	hvc #0
	ret
