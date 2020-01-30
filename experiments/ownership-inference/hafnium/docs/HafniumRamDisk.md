# Hafnium RAM disk

Hafnium expects to find the following files in the root directory of its RAM
disk:

*   `vmlinuz` -- the kernel of the primary VM.
*   `initrd.img` -- the initial ramdisk of the primary VM.
*   kernels for the secondary VMs, whose names are described in the manifest.

Follow the [preparing Linux](PreparingLinux.md) instructions to produce
`vmlinuz` and `initrd.img` for a basic Linux primary VM.

## Create a RAM disk for Hafnium

Assuming that a subdirectory called `initrd` contains the files listed in the
previous section, we can build `initrd.img` with the following command:

```shell
cd initrd; find . | cpio -o > ../initrd.img; cd -
```
