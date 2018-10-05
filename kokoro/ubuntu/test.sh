#!/bin/bash

# Note: this assumes that the images have all been built and the current working
# directory is the root of the repo.

# Fail on any error.
set -e
# Fail on any part of a pipeline failing.
set -o pipefail
# Treat unset variables as an error.
set -u
# Display commands being run.
set -x

TIMEOUT="timeout --foreground"
OUT="out/aarch64/qemu"
HFTEST="$TIMEOUT 30s ./test/vm/hftest.py --out $OUT/clang_aarch64 --initrd"

# Run the host unit tests
mkdir -p $OUT/clang_mock_arch/test_log/unit_tests
$TIMEOUT 30s $OUT/clang_mock_arch/unit_tests \
  --gtest_output="xml:$OUT/clang_mock_arch/test_log/unit_tests/sponge_log.xml" \
  | tee $OUT/clang_mock_arch/test_log/unit_tests/sponge_log.log

# Run the tests with a timeout so they can't loop forever.
$HFTEST primary_only_test
$HFTEST primary_with_secondaries_test
