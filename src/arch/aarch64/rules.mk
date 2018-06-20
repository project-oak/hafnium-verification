SRCS += entry.S
SRCS += exceptions.S
SRCS += handler.c
SRCS += mm.c
SRCS += timer.c

OFFSET_SRCS += offsets.c

ifeq ($(GICV2),1)
  SRCS += gicv2.c
endif

ifeq ($(GICV3),1)
  SRCS += gicv3.c
endif

ifeq ($(PL011),1)
  SRCS += pl011.c
endif
