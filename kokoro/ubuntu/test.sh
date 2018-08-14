#!/bin/bash

# Note: this assumes that the images have all been built and the current working
# directory is the root of the repo.

# Fail on any error.
set -e
# Display commands being run.
set -x

TIMEOUT="timeout --foreground"
OUT="out/aarch64/qemu/clang_aarch64"
HFTEST="timeout --foreground 30s ./test/vm/hftest.py --out $OUT --initrd"

# Run the tests with a timeout so they can't loop forever.
$HFTEST primary_only_test
$HFTEST primary_with_secondary_test
