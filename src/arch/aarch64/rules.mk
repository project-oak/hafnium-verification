SRCS += entry.S
SRCS += exceptions.S
SRCS += handler.c
SRCS += mm.c

OFFSET_SRCS += offsets.c

ifeq ($(PL011),1)
  SRCS += pl011.c
endif
