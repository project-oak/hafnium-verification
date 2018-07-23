.section .init.image, "ax"

.global image_entry
image_entry:
    adr         x0, kstack + 4096
    mov         sp, x0
2:
    bl          kmain
3:
    b           3b
