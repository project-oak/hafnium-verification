OUT ?= out

GN ?= ../gn/out/gn
NINJA ?= ninja

# Configure the build arguments
GCC ?= false
ARCH ?= aarch64
PLATFORM ?= qemu

all: $(OUT)/build.ninja
	@$(NINJA) -C $(OUT)

$(OUT)/build.ninja: $(GN) $(OUT)/args.gn
	@$(GN) gen $(OUT)

# Configure the build by loading the configuration arguments for the
# architecture and platform
$(OUT)/args.gn: build/arch/$(ARCH)/$(PLATFORM).args
	@echo Copying config for $(ARCH) on $(PLATFORM)
	@mkdir -p $(OUT)
	@echo "arch = \"$(ARCH)\"" >> $@
	@echo "use_gcc = $(GCC)" >> $@
	@echo >> $@
	@cat $< >> $@

$(GN):
	git clone https://gn.googlesource.com/gn ../gn
	cd ../gn && python build/gen.py
	ninja -C ../gn/out

clean:
	@$(NINJA) -C $(OUT) -t clean

clobber:
	rm -rf $(OUT)

# see .clang-format
format:
	@find src/ -name *.c -o -name *.h | xargs clang-format -style file -i
	@find inc/ -name *.c -o -name *.h | xargs clang-format -style file -i
	@find . -name *.gn -o -name *.gni -exec $(GN) format {} \;

# TODO: get this working again. Need to extract a compile database to get the correct args.
# see .clang-tidy
# tidy: $(GLOBAL_OFFSETS)
# 	@find $(ROOT_DIR)src/ -name *.c -exec clang-tidy {} -fix -- -target $(TARGET) $(COPTS) \;
