musl was built with the following commands, for a Hafnium checkout in `$HAFNIUM`:

```
$ export CROSS_COMPILE=$HAFNIUM/prebuilts/linux-x64/clang/bin/llvm-
$ export CC=$HAFNIUM/prebuilts/linux-x64/clang/bin/clang
$ export CFLAGS="-target aarch64-linux-musleabi -fpic"
$ ./configure --prefix=$HAFNIUM/prebuilts/linux-aarch64/musl --exec-prefix=$HAFNIUM/prebuilts/linux-x64/musl --target=aarch64 --disable-shared --disable-wrapper
$ make -j32
$ make
$ make install
```
