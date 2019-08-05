# Hafnium RAM disk

Hafnium expects to find the following files in the root directory of its RAM
disk:

*   `vmlinuz` -- the kernel of the primary VM.
*   `initrd.img` -- the initial ramdisk of the primary VM.
*   `vms.txt` -- optionally describes the secondary VMs.
*   kernels for the secondary VMs, whose names are described in `vms.txt`.

Follow the [preparing Linux](PreparingLinux.md) instructions to produce
`vmlinuz` and `initrd.img` for a basic Linux primary VM.

## Format of `vms.txt` file

The format is currently one line per secondary VM, with the following format:

```shell
<memory-size-in-bytes> <number-of-cpus> <kernel-filename>
```

For example, the following defines two secondary VMs, the first one with 1MB of
memory, 2 CPUs and kernel image called `kernel0`, while the second one has 2MB
of memory, 4 CPUs and a kernel image called `kernel1`.

```shell
1048576 2 kernel0
2097152 4 kernel1
```

## Create a RAM disk for Hafnium

Assuming that a subdirectory called `initrd` contains the files listed in the
previous section, we can build `initrd.img` with the following command:

```shell
cd initrd; find . | cpio -o > ../initrd.img; cd -
```
