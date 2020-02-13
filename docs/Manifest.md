# Hafnium Manifest

## Format

The format of the manifest is a simple DeviceTree overlay:

```
/dts-v1/;
/plugin/;

&{/} {
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

Note: `&{/}` is a syntactic sugar expanded by the DTC compiler. Make sure to
use the DTC in `prebuilts/` as the version packaged with your OS may not support
it yet.

## Example

The following manifest defines two secondary VMs, the first one with 1MB of
memory, 2 CPUs and kernel image called `kernel0` (matches filename in Hafnium's
[ramdisk](HafniumRamDisk.md)), while the second one has 2MB of memory, 4 CPUs
and a kernel image called `kernel1`.

```
/dts-v1/;
/plugin/;

&{/} {
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
