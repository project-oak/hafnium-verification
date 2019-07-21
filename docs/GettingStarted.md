# Getting started

## Getting the source code

``` shell
git clone --recurse-submodules https://hafnium.googlesource.com/hafnium && (cd hafnium && f=`git rev-parse --git-dir`/hooks/commit-msg ; curl -Lo $f https://gerrit-review.googlesource.com/tools/hooks/commit-msg ; chmod +x $f)
```

To upload a commit for review:

``` shell
git push origin HEAD:refs/for/master
```

Browse source at https://hafnium.googlesource.com/hafnium.
Review CLs at https://hafnium-review.googlesource.com/.

See details of [how to contribute](../CONTRIBUTING.md).

## Compiling the hypervisor

Install prerequisites:

``` shell
sudo apt install make binutils-aarch64-linux-gnu aarch64-linux-gnu-gcc device-tree-compiler libssl-dev flex bison
```

By default, the hypervisor is built with clang for a few target platforms along
with tests. Each project in the `project` directory specifies a root
configurations of the build. Adding a project is the preferred way to extend
support to new platforms. The target project that is built is selected by the
`PROJECT` make variable, the default project is 'reference'.

``` shell
make PROJECT=<project_name>
```

The compiled image can be found under `out/<project>`, for example the QEMU
image is at `out/reference/qemu_aarch64_clang/hafnium.bin`.

## Running on QEMU

You will need at least version 2.9 for QEMU. The following command line can be
used to run Hafnium on it:

``` shell
qemu-system-aarch64 -M virt,gic_version=3 -cpu cortex-a57 -nographic -machine virtualization=true -kernel out/reference/qemu_aarch64_clang/hafnium.bin
```

Though it is admittedly not very useful because it doesn't have any virtual
machines to run. Follow the [Hafnium RAM disk](HafniumRamDisk.md) instructions
to create an initial RAM disk for Hafnium with Linux as the primary VM.

The following command line will run Hafnium, with the RAM disk just created,
which will then boot into the primary Linux VM:

``` shell
qemu-system-aarch64 -M virt,gic_version=3 -cpu cortex-a57 -nographic -machine virtualization=true -kernel out/reference/qemu_aarch64_clang/hafnium.bin -initrd initrd.img -append "rdinit=/sbin/init"
```

## Running tests

After building, presubmit tests can be run with the following command line:

``` shell
./kokoro/ubuntu/test.sh
```

Read about [testing](Testing.md) for more details about the tests.
