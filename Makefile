OUT ?= out

# Set path to prebuilts used in the build.
UNNAME_S := $(shell uname -s | tr '[:upper:]' '[:lower:]')
PREBUILTS := $(PWD)/prebuilts/$(UNNAME_S)-x64
GN ?= $(PREBUILTS)/gn/gn
NINJA ?= $(PREBUILTS)/ninja/ninja
export PATH := $(PREBUILTS)/clang/bin:$(PATH)

# Configure the build arguments.
GCC ?= false
ARCH ?= aarch64
PLATFORM ?= qemu

.PHONY: all
all: $(OUT)/build.ninja
	@$(NINJA) -C $(OUT)

$(OUT)/build.ninja: $(OUT)/args.gn
	@$(GN) --export-compile-commands gen $(OUT)

# Configure the build by loading the configuration arguments for the
# architecture and platform.
$(OUT)/args.gn: build/arch/$(ARCH)/$(PLATFORM).args
	@echo Copying config for $(ARCH) on $(PLATFORM)
	@mkdir -p $(OUT)
	@echo "arch = \"$(ARCH)\"" >> $@
	@echo "use_gcc = $(GCC)" >> $@
	@echo >> $@
	@cat $< >> $@

.PHONY: clean
clean:
	@$(NINJA) -C $(OUT) -t clean
	rm -f $(OUT)/args.gn

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
	@find . -name *.gn -o -name *.gni -exec $(GN) format {} \;

# see .clang-tidy.
.PHONY: tidy
tidy: $(OUT)/build.ninja
	@$(NINJA) -C $(OUT)
	@echo "Tidying..."
	@find src/ -name *.c -exec clang-tidy -p $(OUT) -fix {} \;
	@find test/ -name *.c -exec clang-tidy -p $(OUT) -fix {} \;

.PHONY: check
check: $(OUT)/build.ninja
	@$(NINJA) -C $(OUT)
	@echo "Checking..."
	@find src/ -name *.c -exec clang-check -p $(OUT) -analyze {} \;
	@find test/ -name *.c -exec clang-check -p $(OUT) -analyze {} \;
