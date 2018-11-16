# Set path to prebuilts used in the build.
UNNAME_S := $(shell uname -s | tr '[:upper:]' '[:lower:]')
PREBUILTS := $(PWD)/prebuilts/$(UNNAME_S)-x64
GN ?= $(PREBUILTS)/gn/gn
NINJA ?= $(PREBUILTS)/ninja/ninja
export PATH := $(PREBUILTS)/clang/bin:$(PATH)

# Place builds for different architectures and platforms in different
# directories.
OUT ?= out
OUT_DIR = out

.PHONY: all
all: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)

$(OUT_DIR)/build.ninja:
	@$(GN) --export-compile-commands gen $(OUT_DIR)

.PHONY: clean
clean:
	@$(NINJA) -C $(OUT_DIR) -t clean

.PHONY: clobber
clobber:
	rm -rf $(OUT)

# see .clang-format.
.PHONY: format
format:
	@echo "Formatting..."
	@find src/ -name \*.c -o -name \*.cc -o -name \*.h | xargs clang-format -style file -i
	@find inc/ -name \*.c -o -name \*.cc -o -name \*.h | xargs clang-format -style file -i
	@find test/ -name \*.c -o -name \*.cc -o -name \*.h | xargs clang-format -style file -i
	@find . \( -name \*.gn -o -name \*.gni \) | xargs -n1 $(GN) format

# see .clang-tidy.
.PHONY: tidy
tidy: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)
	@echo "Tidying..."
	# TODO: enable readability-magic-numbers once there are fewer violations.
	# TODO: enable for c++ tests as it currently gives spurious errors.
	@find src/ \( -name \*.c \) | xargs clang-tidy -p $(OUT_DIR) -fix
	@find test/ \( -name \*.c \) | xargs clang-tidy -p $(OUT_DIR) -fix

.PHONY: check
check: $(OUT_DIR)/build.ninja
	@$(NINJA) -C $(OUT_DIR)
	@echo "Checking..."
	# TODO: enable for c++ tests as it currently gives spurious errors.
	@find src/ \( -name \*.c \) | xargs clang-check -p $(OUT_DIR) -analyze -fix-what-you-can
	@find test/ \( -name \*.c \) | xargs clang-check -p $(OUT_DIR) -analyze -fix-what-you-can

.PHONY: license
license:
	@find src/ -name \*.S -o -name \*.c -o -name \*.cc -o -name \*.h | xargs -n1 python build/license.py --style c
	@find inc/ -name \*.S -o -name \*.c -o -name \*.cc -o -name \*.h | xargs -n1 python build/license.py --style c
	@find test/ -name \*.S -o -name \*.c -o -name \*.cc -o -name \*.h | xargs -n1 python build/license.py --style c
	@find build/ -name \*.py| xargs -n1 python build/license.py --style hash
	@find test/ -name \*.py| xargs -n1 python build/license.py --style hash
	@find . \( -name \*.gn -o -name \*.gni \) | xargs -n1 python build/license.py --style hash
