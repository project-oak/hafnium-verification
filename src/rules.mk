SRCS += alloc.c
SRCS += api.c
SRCS += cpio.c
SRCS += cpu.c
SRCS += fdt.c
SRCS += main.c
SRCS += mm.c
SRCS += std.c
SRCS += vm.c

ifeq ($(DEBUG),1)
  SRCS += dlog.c
endif
