# Testing

Testing of Hafnium is currently evolving. There are basic tests running on QEMU
but we want more and more kinds of tests e.g. unit tests.

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

### `hftest`

Having a framework for tests makes them easier to read and write. `hftest` is a
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
