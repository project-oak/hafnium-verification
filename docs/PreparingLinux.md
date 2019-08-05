# Preparing Linux

To boot Linux, a kernel image (`vmlinuz`) and a suitable initial RAM disk
(`initrd.img`) need to be created.

## Build the kernel

The Linux kernel for the primary VM can be built using the following
command-line:

```shell
git clone https://github.com/torvalds/linux.git
cd linux
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make defconfig
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make -j24
```

The compiled image is stored in `arch/arm64/boot/Image`. This will later be
copied to the Hafnium RAM disk's root as `vmlinuz`.

## Build the kernel Module

From the Hafnium root directory, the following commands can be used to compile
the kernel module, replacing `<kernel-path>` with the path to the kernel checked
out in the previous section:

```shell
cd hafnium/driver/linux/
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- KERNEL_PATH=<kernel-path> make
```

The compiled module is called `hafnium.ko`, and will later be copied into the
RAM disk for Linux.

## Build Busybox

To make Linux useful, it needs a shell. These following instructions will
construct a file system for the Linux RAM disk with the BusyBox shell as the
init process.

```shell
git clone git://busybox.net/busybox.git
cd busybox
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make defconfig
ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- make menuconfig
```

At this point you should ensure that the option `Settings > Build static binary
(no shared libs)` is selected. Then you can proceed with the following commands:

```shell
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
```

## Create a RAM disk for Linux

At this point you can copy into the current directory additional files you may
want in the RAM disk, for example, the kernel module built in the previous
section. Assuming the BusyBox root directory is in the same parent directory as
the Hafnium root directory:

```shell
cp ../../hafnium/driver/linux/hafnium.ko .
```

Then run the following commands:

```shell
find . | cpio -o -H newc | gzip > ../initrd.img
cd ..
```

The resulting file is `initrd.img`. It should be copied to the Hafnium RAM
disk's root.
