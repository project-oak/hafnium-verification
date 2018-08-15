# Set path to prebuilts used in the build.
UNNAME_S := $(shell uname -s | tr '[:upper:]' '[:lower:]')
PREBUILTS := $(PWD)/prebuilts/$(UNNAME_S)-x64
GN ?= $(PREBUILTS)/gn/gn
NINJA ?= $(PREBUILTS)/ninja/ninja
export PATH := $(PREBUILTS)/clang/bin:$(PATH)

# Configure the build arguments.
ARCH ?= aarch64
PLATFORM ?= qemu
GCC ?= false

# Place builds for different architectures and platforms in different
# directories.
OUT ?= out
OUT_DIR = out/$(ARCH)/$(PLATFORM)

.PHONY: all
all: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)

$(OUT_DIR)/build.ninja: $(OUT_DIR)/args.gn
	@$(GN) --export-compile-commands gen $(OUT_DIR)

# Configure the build by loading the configuration arguments for the
# architecture and platform.
$(OUT_DIR)/args.gn: build/arch/$(ARCH)/$(PLATFORM).args
	@echo Copying config for $(ARCH) on $(PLATFORM)
	@mkdir -p $(OUT_DIR)
	@echo "arch = \"$(ARCH)\"" >> $@
	@echo "use_gcc = $(GCC)" >> $@
	@echo >> $@
	@cat $< >> $@

.PHONY: clean
clean:
	@$(NINJA) -C $(OUT_DIR) -t clean
	rm -f $(OUT_DIR)/args.gn

.PHONY: clobber
clobber:
	rm -rf $(OUT)

# see .clang-format.
.PHONY: format
format:
	@echo "Formatting..."
	@find src/ -name *.c -o -name *.h | xargs clang-format -style file -i
	@find inc/ -name *.c -o -name *.h | xargs clang-format -style file -i
	@find test/ -name *.c -o -name *.h | xargs clang-format -style file -i
	@find . \( -name *.gn -o -name *.gni \) -exec $(GN) format {} \;

# see .clang-tidy.
.PHONY: tidy
tidy: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)
	@echo "Tidying..."
	@find src/ -name *.c -exec clang-tidy -p $(OUT_DIR) -fix {} \;
	@find test/ -name *.c -exec clang-tidy -p $(OUT_DIR) -fix {} \;

.PHONY: check
check: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)
	@echo "Checking..."
	@find src/ -name *.c -exec clang-check -p $(OUT_DIR) -analyze {} \;
	@find test/ -name *.c -exec clang-check -p $(OUT_DIR) -analyze {} \;
