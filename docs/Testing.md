# Testing

## Overview

Hafnium has 4 main kinds of tests:

1.  Host tests
    *   Unit tests of core functionality, e.g. page table manipulation.
    *   Source in `src/*_test.cc`.
    *   Using the [Google Test](https://github.com/google/googletest) framework,
        built against 'fake' architecture (`src/arch/fake`).
1.  Arch tests
    *   Architecture-specific unit tests, e.g. MMU setup.
    *   Source under `test/arch`.
    *   Using our own _hftest_ framework, with `standalone_main.c`.
    *   Build own hypervisor image, run in EL2.
1.  VM API tests
    *   Exercise hypervisor API from both primary and secondary VMs.
    *   Source under `test/vmapi`.
    *   Tests are run from the primary VM under a normal build of the Hafnium
        hypervisor, possibly communicating with a helper service in one or more
        secondary VMs.
    *   Using our own _hftest_ framework, with `standalone_main.c` for the
        primary VM and `hftest_service.c` for secondary VMs.
    *   Build own primary and secondary VMs, run in EL1 under actual Hafnium
        image.
1.  Linux tests
    *   Exercise the Hafnium Linux kernel module.
    *   Source under `test/linux`.
    *   Tests are run from userspace (PID 1) under Linux in the primary VM under
        Hafnium, possibly with other secondary VMs.
    *   Using our own _hftest_ framework, with `linux_main.c`.

Host tests run directly on the host machine where they are built, whereas the
other 3 types can run under an emulator such as QEMU, or on real hardware.

## Presubmit

Presubmit builds everything, runs all tests and checks the source for formatting
and lint errors. This can be run locally with:

```shell
./kokoro/ubuntu/build.sh
```

Or to just run the tests after having built everything manually run:

```shell
./kokoro/ubuntu/test.sh
```

## QEMU tests

These tests boot Hafnium on QEMU and the VMs make calls to Hafnium to test its
behaviour.

### hftest

Having a framework for tests makes them easier to read and write. _hftest_ is a
framework to meet the needs of VM based tests for Hafnium. It consists of:

*   assertions
*   test declarations
*   base VM image
*   driver script

Assertions should be familiar from other testing libraries. They make use of
C11's `_Generic` expressions for type genericity.

Test declarations name the test and the suite that the test is part of.
Declarations are converted into descriptors stored in the `.hftest` section of
the VM image which allows the image to inspect the structure of the tests it
contains. The linker sorts the descriptors by their symbol name which is how
descriptors from the same suite are grouped together for easier parsing.

The base VM image offers a command line interface, via the bootargs, to query
the tests in the image and to run specific tests. The driver script uses this
interface to execute tests, each with a fresh QEMU boot to give a fresh
environment.
