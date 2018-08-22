# Getting started

## Getting access

Read access to the source is provided to all Googlers (members of
`nonconf-mirror@prod`, to be precise). Permission to submit CLs requires
membership of `hafnium-access@prod`. Full administrative rights are only granted
to members of `hafnium-admin@prod`.

## Getting the source code

``` shell
git clone --recurse-submodules sso://hafnium/hafnium && (cd hafnium && f=`git rev-parse --git-dir`/hooks/commit-msg ; curl -Lo $f https://gerrit-review.googlesource.com/tools/hooks/commit-msg ; chmod +x $f)
```

To upload a commit for review:

``` shell
git push origin HEAD:refs/for/master
```
Browse source at [go/hafnium-repo](https://goto.google.com/hafnium-repo).
Review CLs at [go/hafnium-review](https://goto.google.com/hafnium-review).

## Compiling the hypervisor

By default, the hypervisor is built with clang for an aarch64 QEMU target by
running:

``` shell
make
```

The compiled image can be found at `out/aarch64/qemu/clang_aarch64/hafnium.bin`.

To build for the HiKey board, change the target platform:

``` shell
PLATFORM=hikey make
```

To build using gcc instead of clang, the aarch64 variant must be installed:

``` shell
sudo apt install gcc-aarch64-linux-gnu
GCC=true make
```
## Running on QEMU

You will need at least version 2.9 for QEMU. The following command line can be
used to run Hafnium on it:

``` shell
qemu-system-aarch64 -M virt -cpu cortex-a57 -nographic -machine virtualization=true -kernel out/aarch64/qemu/clang_aarch64/hafnium.bin
```

Though it is admittedly not very useful because it doesn't have any virtual
machines to run. Follow the [Hafnium RAM disk](HafniumRamDisk.md) instructions
to create an initial RAM disk for Hafnium with Linux as the primary VM.

The following command line will run Hafnium, with the RAM disk just created,
which will then boot into the primary Linux VM:

``` shell
qemu-system-aarch64 -M virt -cpu cortex-a57 -nographic -machine virtualization=true -kernel out/aarch64/qemu/clang_aarch64/hafnium.bin -initrd initrd.img -append "rdinit=/sbin/init"
```

## Running tests

After building, presubmit tests can be run with the following command line:

``` shell
./kokoro/ubuntu/test.sh
```

Read about [testing](Testing.md) for more details about the tests.
