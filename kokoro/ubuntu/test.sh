#!/bin/bash

# Note: this assumes that the images have all been built and the current working
# directory is the root of the repo.

# Fail on any error.
set -e
# Display commands being run.
set -x

TIMEOUT="timeout --foreground"
QEMU="./prebuilts/linux-x64/qemu/qemu-system-aarch64 -M virt -cpu cortex-a57 -m 8M -machine virtualization=true -nographic -nodefaults -serial stdio"
HAFNIUM="out/clang_aarch64/hafnium.bin"
INITRD="out/clang_aarch64/initrd"

# Run the QEMU tests with a timeout so they can't loop forever.
$TIMEOUT 5s $QEMU -kernel $HAFNIUM -initrd $INITRD/primary_only_test.img
$TIMEOUT 5s $QEMU -kernel $HAFNIUM -initrd $INITRD/primary_with_secondary_test.img
