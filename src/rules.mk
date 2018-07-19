SRCS += alloc.c
SRCS += api.c
SRCS += cpio.c
SRCS += cpu.c
SRCS += load.c
SRCS += main.c
SRCS += memiter.c
SRCS += mm.c
SRCS += std.c
SRCS += vm.c

ifeq ($(DEBUG),1)
  SRCS += dlog.c
endif

ifeq ($(USE_FDT),1)
  SRCS += fdt.c
  SRCS += fdt_handler.c
endif
