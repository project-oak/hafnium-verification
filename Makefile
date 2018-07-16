OUT ?= out

GN ?= ../gn/out/gn
NINJA ?= ninja

all: $(OUT)/build.ninja
	@$(NINJA) -C $(OUT)

out/build.ninja: $(GN)
	@$(GN) gen $(OUT)

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
