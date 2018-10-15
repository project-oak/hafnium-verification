#!/bin/bash
#
# Copyright 2018 Google LLC
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
OUT="out/aarch64/qemu"
HFTEST="$TIMEOUT 30s ./test/vm/hftest.py --out $OUT/clang_aarch64 --initrd"

# Run the host unit tests
mkdir -p $OUT/clang_fake_arch/test_log/unit_tests
$TIMEOUT 30s $OUT/clang_fake_arch/unit_tests \
  --gtest_output="xml:$OUT/clang_fake_arch/test_log/unit_tests/sponge_log.xml" \
  | tee $OUT/clang_fake_arch/test_log/unit_tests/sponge_log.log

# Run the tests with a timeout so they can't loop forever.
$HFTEST primary_only_test
$HFTEST primary_with_secondaries_test
