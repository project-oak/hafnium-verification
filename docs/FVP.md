# FVP

Arm offers a series of emulators known as Fixed Virtual Platforms (FVPs), which
simulate various processors. They are generally more accurate to the hardware
than QEMU, at the cost of being considerably slower. We support running
[tests](Testing.md) on the FVP as well as QEMU.

## Set up

1.  Download the
    [Armv8-A Base Platform FVP](https://developer.arm.com/products/system-design/fixed-virtual-platforms)
    from Arm.
1.  Unzip it to a directory called `fvp` alongside the root directory of your
    Hafnium checkout.

## Running tests

To run tests with the FVP instead of QEMU, from the root directory of your
Hafnium checkout:

```shell
$ make && kokoro/ubuntu/test.sh --fvp
```

See the `fvp` function in
[`hftest.py`](http://cs/hafnium/test/hftest/hftest.py?q=symbol:fvp) for details
on how this works.

## Other resources

When running tests under the FVP we also use a prebuilt version of TF-A, which
is checked in under
[`prebuilts/linux-aarch64/arm-trusted-firmware/`](https://hafnium.googlesource.com/hafnium/prebuilts/+/refs/heads/master/linux-aarch64/arm-trusted-firmware/).
The
[README](https://hafnium.googlesource.com/hafnium/prebuilts/+/refs/heads/master/linux-aarch64/arm-trusted-firmware/README.md)
there has details on how it was built. The source code is available from the
[Arm Trusted Firmware site](https://developer.trustedfirmware.org/dashboard/view/6/).

Documentation of the FVP (including memory maps) is
[available from Arm](https://static.docs.arm.com/100966/1101/fast_models_fvp_rg_100966_1101_00_en.pdf).
