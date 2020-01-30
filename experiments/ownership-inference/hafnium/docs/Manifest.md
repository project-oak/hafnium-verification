# Hafnium Manifest

[TOC]

## Format

The format of the manifest is a simple DeviceTree overlay:

```
/dts-v1/;
/plugin/;

&{/} {
	hypervisor {
		compatible = "hafnium,hafnium";

		vm1 {
			debug_name = "name";
			kernel_filename = "vmlinuz";
			ramdisk_filename = "initrd.img";
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

Note: `&{/}` is a syntactic sugar expanded by the DTC compiler. Make sure to
use the DTC in `prebuilts/` as the version packaged with your OS may not support
it yet.

## Example

The following manifest defines a primary VM with two secondary VMs. The first
secondary VM has 1MB of memory, 2 CPUs and kernel image called `kernel0`
(matches filename in Hafnium's [ramdisk](HafniumRamDisk.md)). The second has 2MB
of memory, 4 CPUs and, by omitting the `kernel_filename` property, a kernel
preloaded into memory. The primary VM is given all remaining memory, the same
number of CPUs as the hardware, a kernel image called `vmlinuz` and a ramdisk
`initrd.img`. Secondaries cannot have a ramdisk.

```
/dts-v1/;
/plugin/;

&{/} {
	hypervisor {
		compatible = "hafnium,hafnium";

		vm1 {
			debug_name = "primary VM";
			kernel_filename = "vmlinuz";
			ramdisk_filename = "initrd.img";

			smc_whitelist = <
				0x04000000
				0x3200ffff
				>;
		};

		vm2 {
			debug_name = "secondary VM 1";
			kernel_filename = "kernel0";
			vcpu_count = <2>;
			mem_size = <0x100000>;

			smc_whitelist_permissive;
		};

		vm3 {
			debug_name = "secondary VM 2";
			vcpu_count = <4>;
			mem_size = <0x200000>;
		};
	};
};
```

## Compiling

Hafnium expects the manifest as part of the board FDT, i.e. DeviceTree in binary
format (DTB).

First, compile the manifest into a DTBO (binary overlay):
```shell
prebuilts/linux-x64/dtc/dtc -I dts -O dtb --out-version 17 -o manifest.dtbo <manifest_source_file>
```

Then overlay it with the DTB of your board:
```shell
prebuilts/linux-x64/dtc/fdtoverlay -i <board DTB> -o <output DTB> manifest.dtbo
```
