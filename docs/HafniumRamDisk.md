# Hafnium RAM disk

Hafnium expects to find the following files in the root directory of its RAM
disk:

*   `vmlinuz` -- the kernel of the primary VM.
*   `initrd.img` -- the initial ramdisk of the primary VM.
*   `manifest.dtb` -- hypervisor configuration file.
*   kernels for the secondary VMs, whose names are described in the manifest.

Follow the [preparing Linux](PreparingLinux.md) instructions to produce
`vmlinuz` and `initrd.img` for a basic Linux primary VM.

## Manifest file

The format is currently a simple Device Tree:

```
/dts-v1/;

/ {
	hypervisor {
		vm1 {
			debug_name = "name";
		};

		vm2 {
			debug_name = "name";
			kernel_filename = "filename";
			vcpu_count = <N>;
			mem_size = <M>;
		};
		...
	};
};
```

For example, the following defines two secondary VMs, the first one with 1MB of
memory, 2 CPUs and kernel image called `kernel0`, while the second one has 2MB
of memory, 4 CPUs and a kernel image called `kernel1`.

```
/dts-v1/;

/ {
	hypervisor {
		vm1 {
			debug_name = "primary VM";
		};

		vm2 {
			debug_name = "secondary VM 1";
			kernel_filename = "kernel0";
			vcpu_count = <2>;
			mem_size = <0x100000>;
		};

		vm3 {
			debug_name = "secondary VM 2";
			kernel_filename = "kernel1";
			vcpu_count = <4>;
			mem_size = <0x200000>;
		};
	};
};
```

Hafnium expects the manifest in Device Tree Blob format. Compile it with:
```shell
dtc -I dts -O dtb --out-version 17 -o manifest.dtb <manifest_source_file>
```

## Create a RAM disk for Hafnium

Assuming that a subdirectory called `initrd` contains the files listed in the
previous section, we can build `initrd.img` with the following command:

```shell
cd initrd; find . | cpio -o > ../initrd.img; cd -
```
