arm-trusted-firmware was built with the following commands:

```
$ make CROSS_COMPILE=aarch64-linux-gnu- PLAT=fvp FVP_HW_CONFIG_DTS=fdts/fvp-base-gicv3-psci-1t.dts PRELOADED_BL33_BASE=0x80000000 ARM_LINUX_KERNEL_AS_BL33=1 ARM_PRELOADED_DTB_BASE=0x82000000 RESET_TO_BL31=1 ENABLE_PIE=0 V=1 all fip -j16
$ make CROSS_COMPILE=aarch64-linux-gnu- PLAT=rpi4 -j16
$ cp build/fvp/release/bl31.bin ../hafnium/prebuilts/linux-aarch64/arm-trusted-firmware/fvp/bl31.bin
$ cp build/rpi4/release/bl31.bin ../hafnium/prebuilts/linux-aarch64/arm-trusted-firmware/rpi4/bl31.bin
$ cp license.rst ../hafnium/prebuilts/linux-aarch64/arm-trusted-firmware/LICENSE
$ dtc -I dtb -O dts build/fvp/release/fdts/fvp-base-gicv3-psci-1t.dtb -o ../hafnium/prebuilts/linux-aarch64/arm-trusted-firmware/fvp/fvp-base-gicv3-psci-1t.dts
```
