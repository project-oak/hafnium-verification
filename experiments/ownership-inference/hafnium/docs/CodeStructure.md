# Code structure

The Hafnium repository contains Hafnium itself, along with unit tests and
integration tests, a small client library for VMs, a Linux kernel module for the
primary VM, prebuilt binaries of tools needed for building it and running tests.
Everything is built with [GN](https://gn.googlesource.com/gn/).

Hafnium can be built for an **architecture**, currently including:

*   `aarch64`: 64-bit Armv8
*   `fake`: A dummy architecture used for running unit tests on the host system.

And for a **platform**, such as:

*   `aem_v8a_fvp`: The Arm [Fixed Virtual Platform](FVP.md) emulator.
*   `qemu_aarch64`: QEMU emulating an AArch64 device.
*   `rpi4`: A Raspberry Pi 4 board.

Each platform has a single associated architecture.

The source tree is organised as follows:

*   [`build`](../build): Common GN configuration, build scripts, and linker
    script.
*   [`docs`](.): Documentation
*   [`driver/linux`](../driver/linux): Linux kernel driver for Hafnium, for use
    in the primary VM.
*   [`inc`](../inc): Header files...
    *   [`hf`](../inc/hf): ... internal to Hafnium
        *   [`arch`](../inc/hf/arch): Architecture-dependent modules, which have
            a common interface but separate implementations per architecture.
            This includes details of CPU initialisation, exception handling,
            timers, page table management, and other system registers.
        *   [`plat`](../inc/hf/plat): Platform-dependent modules, which have a
            common interface but separate implementations per platform. This
            includes details of the boot flow, and a UART driver for the debug
            log console.
    *   [`system`](../inc/system): ... which are included by the `stdatomic.h`
        which we use from Android Clang but not really needed, so we use dummy
        empty versions.
    *   [`vmapi/hf`](../inc/vmapi/hf): ... for the interface exposed to VMs.
*   [`kokoro`](../kokoro): Scripts and configuration for continuous integration
    and presubmit checks.
*   [`prebuilts`](../prebuilts): Prebuilt binaries needed for building Hafnium
    or running tests.
*   [`project`](../project): Configuration and extra code for each **project**.
    A project is a set of one or more _platforms_ (see above) that are built
    together. Hafnium comes with the [`reference`](../project/reference) project
    for running it on some common emulators and development boards. To port
    Hafnium to a new board, you can create a new project under this directory
    with the platform or platforms you want to add, without affecting the core
    Hafnium code.
*   [`src`](../src): Source code for Hafnium itself in C and assembly, and
    [unit tests](Testing.md) in C++.
    *   [`arch`](../src/arch): Implementation of architecture-dependent modules.
*   [`test`](../test): [Integration tests](Testing.md)
    *   [`arch`](../test/arch): Tests for components of Hafnium that need to be
        run on a real architecture.
    *   [`hftest`](../test/hftest): A simple test framework that supports
        running tests standalone on bare metal, in VMs under Hafnium, or as
        user-space binaries under Linux under Hafnium.
    *   [`linux`](../test/linux): Tests which are run in a Linux VM under
        Hafnium.
    *   [`vmapi`](../test/vmapi): Tests which are run in minimal test VMs under
        Hafnium.
        *   [`arch`](../test/vmapi/arch): Tests which are rely on specific
            architectural details such as the GIC version.
        *   [`primary_only`](../test/vmapi/primary_only): Tests which run only a
            single (primary) VM.
        *   [`primary_with_secondaries`](../test/vmapi/primary_with_secondaries):
            Test which run with a primary VM and one or more secondary VMs to
            test how they interact.
*   [`third_party`](../third_party): Third party code needed for building
    Hafnium.
*   [`vmlib`](../vmlib): A small client library for VMs running under Hafnium.
