# Hafnium

Hafnium is a hypervisor, initially supporting aarch64 (64-bit ARMv8 CPUs).

## Getting the source code

``` shell
mkdir hafnium
cd hafnium
repo init -u sso://hafnium/manifest
repo sync -j4
```

## Building

### One-time setup
You will need a cross-compilation toolchain, for example, `aarch64-linux-gnu`, which can be installed with `apt-get` using the following command-line:
``` shell
sudo apt-get install gcc-aarch64-linux-gnu
```

Makefiles use the `CROSS_COMPILE` variable to specify the prefix of the tools; in the case above it is `aarch64-linux-gnu-` (note the trailing dash). In the examples that follow, we will assume that this toolchain is installed and available for use.

### Compiling the hypervisor

The hypervisor proper is in the `hafnium` subdirectory. It can be built for QEMU using the following command:

``` shell
CROSS_COMPILE=aarch64-linux-gnu- make
```

The compiled binary is stored in `out/aarch64/qemu/hafnium.bin`.

## Running on QEMU

You will need at least version 2.9 for QEMU. The following command line can be used to run Hafnium on it:

``` shell
qemu-system-aarch64 -M virt -cpu cortex-a57 -nographic -machine virtualization=true -kernel out/aarch64/qemu/hafnium.bin
```

Though it is admittedly not very useful because it doesn't have any virtual machines to run. The next sections describe how to build an image that can be run using the following command-line:
``` shell
qemu-system-aarch64 -M virt -cpu cortex-a57 -nographic -machine virtualization=true -kernel out/aarch64/qemu/hafnium.bin -initrd initrd.img -append "rdinit=/sbin/init"
```

## Hafnium RAM disk

Hafnium expects to find the following files in the root directory of its ramdisk:

* `vmlinuz` -- the kernel of the primary VM.
* `initrd.img` -- the initial ramdisk of the primary VM.
* `vms.txt` -- optionally describes the secondary VMs.
* kernels for the secondary VMs, whose names vary and are described in `vms.txt`.

### Format of `vms.txt` file
The format is currently one line per secondary VM, with the following format:
``` shell
<memory-size-in-bytes> <number-of-cpus> <kernel-filename>
```

For example, the following defines two secondary VMs, the first one with 1MB of memory, 2 CPUs and kernel image called `kernel0`, while the second one has 2MB of memory, 4 CPUs and a kernel image called  `kernel1`.
``` shell
1048576 2 kernel0
2097152 4 kernel1
```

### Creating a hafnium RAM disk

Assuming that a subdirectory called `initrd` contains the files listed in the previous section, we can build `initrd.img` with the following command:
``` shell
cd initrd; find . | cpio -o > ../initrd.img; cd -
```

## Primary VM

### Kernel

The linux kernel for the primary VM can be built using the following command-line:
``` shell
git clone https://github.com/torvalds/linux.git
cd linux
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make defconfig
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make -j24
```

The compiled image is stored in `arch/arm64/boot/Image`. This should be copied to the Hafnium ramdisk's root as `vmlinuz`.

### Busybox RAM disk

An initial ramdisk for the primary VM containing busybox can be built with the following commands:

``` shell
git clone git://busybox.net/busybox.git
cd busybox
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make defconfig
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make menuconfig
```

At this point you should ensure that the option `Build static binary (no shared libs)` under `Settings` is selected. Then you can proceed with the following commands:

``` shell
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make -j24
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make install
cd _install
mkdir proc
mkdir sys
mkdir -p etc/init.d
cat <<EOF > etc/init.d/rcS
#!bin/sh
mount -t proc none /proc
mount -t sysfs none /sys
EOF
chmod u+x etc/init.d/rcS
grep -v tty ../examples/inittab > ./etc/inittab
find . | cpio -o -H newc | gzip > ../initrd.img
cd -
```

The resulting file is `initrd.img`. It should be copied to the Hafnium ramdisk's root.
