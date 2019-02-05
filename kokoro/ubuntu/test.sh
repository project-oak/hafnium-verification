#!/bin/bash
#
# Copyright 2018 The Hafnium Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

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
PROJECT="${PROJECT:-reference}"
OUT="out/${PROJECT}"
HFTEST="$TIMEOUT 30s ./test/hftest/hftest.py --out $OUT/qemu_aarch64_clang --log $OUT/kokoro_log"

# Add prebuilt libc++ to the path.
export LD_LIBRARY_PATH=$PWD/prebuilts/linux-x64/clang/lib64

# Run the host unit tests.
mkdir -p $OUT/kokoro_log/unit_tests
$TIMEOUT 30s $OUT/host_fake_clang/unit_tests \
  --gtest_output="xml:$OUT/kokoro_log/unit_tests/sponge_log.xml" \
  | tee $OUT/kokoro_log/unit_tests/sponge_log.log

# Run the tests with a timeout so they can't loop forever.
$HFTEST arch_test
$HFTEST hafnium --initrd test/vmapi/gicv3/gicv3_test
$HFTEST hafnium --initrd test/vmapi/primary_only/primary_only_test
$HFTEST hafnium --initrd test/vmapi/primary_with_secondaries/primary_with_secondaries_test
$HFTEST hafnium --initrd test/linux/linux_test --vm_args "rdinit=/test_binary --"
