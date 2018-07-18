ROOT_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
ifeq ($(ROOT_DIR),./)
  ROOT_DIR :=
endif

#
# Defaults.
#
ARCH ?= aarch64
PLAT ?= qemu
DEBUG ?= 1
NAME := hafnium

# Toolchain
CROSS_COMPILE ?= aarch64-linux-gnu-

ifeq ($(CLANG),1)
  CLANG := clang
endif
GCC ?= gcc

ifdef CLANG
  CC := $(CLANG) -target $(patsubst %-,%,$(CROSS_COMPILE))
else
  CC := $(CROSS_COMPILE)$(GCC)
endif

# Output
OUT := $(ROOT_DIR)out/$(ARCH)/$(PLAT)

all: $(OUT)/$(NAME).bin

# Include platform-specific constants.
include $(ROOT_DIR)src/arch/$(ARCH)/$(PLAT).mk

define include_module
  SRCS :=
  OFFSET_SRCS :=
  include $(ROOT_DIR)$(1)/rules.mk
  GLOBAL_SRCS += $$(addprefix $(1)/,$$(SRCS))
  GLOBAL_OFFSET_SRCS += $$(addprefix $(1)/,$$(OFFSET_SRCS))
endef

#
# Include each module.
#
MODULES := src
MODULES += src/arch/$(ARCH)
GLOBAL_SRCS :=
GLOBAL_OFFSET_SRCS :=
$(foreach mod,$(MODULES),$(eval $(call include_module,$(mod))))

#
# Rules to build C files.
#
COPTS = -mcpu=cortex-a57+nofp
COPTS += -fno-stack-protector
COPTS += -fno-builtin -ffreestanding
COPTS += -g
COPTS += -O2
COPTS += -fpic
COPTS += -std=c11
COPTS += -Wall -Wpedantic -Werror
COPTS += -Wno-extended-offsetof
COPTS += -DDEBUG=$(DEBUG)
COPTS += -MMD -MP -MF $$(patsubst %,%.d,$$@)
COPTS += -DMAX_CPUS=8
COPTS += -DMAX_VMS=16
COPTS += -DSTACK_SIZE=4096
COPTS += -I$(ROOT_DIR)inc
COPTS += -I$(ROOT_DIR)src/arch/$(ARCH)/inc
COPTS += -I$(OUT)/arch/$(ARCH)/inc
COPTS += -DGICD_BASE=$(GICD_BASE)
COPTS += -DGICC_BASE=$(GICC_BASE)
COPTS += -DGICR_BASE=$(GICR_BASE)
COPTS += -DTIMER_IRQ=$(TIMER_IRQ)

ifeq ($(PL011),1)
  COPTS += -DPL011_BASE=$(PL011_BASE)
endif

define build_c
  TGT := $(patsubst %.c,%.o,$(OUT)/$(patsubst src/%,%,$(1)))
  GLOBAL_OBJS += $$(TGT)
  REMAIN_SRCS := $$(filter-out $(1),$$(REMAIN_SRCS))
$$(TGT): $(ROOT_DIR)$(1) | $$(dir $$(TGT))
	$$(info CC $(ROOT_DIR)$1)
	@$(CC) $(COPTS) -c $(ROOT_DIR)$(1) -o $$@
endef

#
# Rules to generate offsets.
#
define gen_offsets
  TMP := $(patsubst src/%,%,$(1))
  TMP := $$(dir $$(TMP))inc/$$(notdir $$(TMP))
  TGT := $$(patsubst %.c,%.h,$(OUT)/$$(TMP))
  GLOBAL_OFFSETS += $$(TGT)
$$(TGT): $(ROOT_DIR)$(1) | $$(dir $$(TGT))
	$$(info GENOFFSET $(ROOT_DIR)$1)
	@$(CC) $(COPTS) -MT $$@ -S -c $(ROOT_DIR)$(1) -o - | \
		grep ^DEFINE_OFFSET -A1 | \
		grep -v ^--$ | \
		sed 's/^DEFINE_OFFSET__\([^:]*\):/#define \1 \\/g' | sed 's/\.xword//g' > $$@
endef

#
# Rules to build S files.
#
define build_S
  TGT := $(patsubst %.S,%.o,$(OUT)/$(patsubst src/%,%,$(1)))
  GLOBAL_OBJS += $$(TGT)
  REMAIN_SRCS := $$(filter-out $(1),$$(REMAIN_SRCS))
$$(TGT): $(ROOT_DIR)$(1) $(GLOBAL_OFFSETS) | $$(dir $$(TGT))
	$$(info AS $(ROOT_DIR)$1)
	@$(CC) $(COPTS) -c $(ROOT_DIR)$(1) -o $$@
endef

#
# Generate the build rules for all .c and .S files.
#
GLOBAL_OBJS :=
GLOBAL_OFFSETS :=
REMAIN_SRCS := $(GLOBAL_SRCS)
$(foreach file,$(filter %.c,$(GLOBAL_OFFSET_SRCS)),$(eval $(call gen_offsets,$(file))))
$(foreach file,$(filter %.c,$(GLOBAL_SRCS)),$(eval $(call build_c,$(file))))
$(foreach file,$(filter %.S,$(GLOBAL_SRCS)),$(eval $(call build_S,$(file))))

#
# Check if there are any source files which we don't know to handle.
#
ifneq ($(REMAIN_SRCS),)
  $(error Don't know how to handle $(REMAIN_SRCS))
endif

#
# Rule to create all output directories.
#
define create_dir
$1:
	@mkdir -p $1
endef
$(foreach name,$(sort $(dir $(GLOBAL_OBJS))),$(eval $(call create_dir,$(name))))
$(foreach name,$(sort $(dir $(GLOBAL_OFFSETS))),$(eval $(call create_dir,$(name))))

#
# Rules to build the hypervisor.
#
$(OUT)/$(NAME): $(GLOBAL_OBJS) $(ROOT_DIR)src/$(NAME).ld
	$(info LD $(ROOT_DIR)src/$(NAME).ld)
	@$(CROSS_COMPILE)ld -g -pie $(GLOBAL_OBJS) -T$(ROOT_DIR)src/$(NAME).ld --defsym PREFERRED_LOAD_ADDRESS=$(LOAD_ADDRESS) -o $@

$(OUT)/$(NAME).bin: $(OUT)/$(NAME)
	$(info OBJCOPY $@)
	@$(CROSS_COMPILE)objcopy -O binary $< $@

clean:
	rm -rf $(ROOT_DIR)out

-include $(patsubst %,%.d,$(GLOBAL_OBJS),$(GLOBAL_OFFSETS))
