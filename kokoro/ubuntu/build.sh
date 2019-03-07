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

# Fail on any error.
set -e
# Fail on any part of a pipeline failing.
set -o pipefail
# Treat unset variables as an error.
set -u
# Display commands being run.
set -x

# Detect server vs local run. Local run should be from the project's root
# directory.
if [ -v KOKORO_JOB_NAME ]
then
	# Server
	cd git/hafnium
else
	# Local
	echo "Testing kokoro build locally..."
fi

CLANG=${PWD}/prebuilts/linux-x64/clang/bin/clang

#
# Step 1: make sure it builds.
#

# Check the hypervisor builds.
make

#
# Step 2: make sure it works.
#

./kokoro/ubuntu/test.sh

#
# Step 3: static analysis.
#

make check
if [[ `git status --porcelain` ]]
then
	echo "Run \`make check\' locally to fix this."
	exit 1
fi

#
# Step 4: make sure the code looks good.
#

make format
if [[ `git status --porcelain` ]]
then
	echo "Run \`make format\' locally to fix this."
	exit 1
fi

make checkpatch

#
# Step 5: make sure there's not lint.
#

make tidy
if [[ `git status --porcelain` ]]
then
	echo "Run \`make tidy\' locally to fix this."
	exit 1
fi

#
# Step 6: make sure all the files have a license.
#

make license
if [[ `git status --porcelain` ]]
then
	echo "Run \`make license\' locally to fix this."
	exit 1
fi

# Step 7: make sure the Linux driver builds and maintains style.
(
export ARCH=arm64 &&
export CROSS_COMPILE=aarch64-linux-gnu- &&
make CC=${CLANG} -C third_party/linux defconfig modules_prepare &&
cd driver/linux &&
make CC=${CLANG} &&
make checkpatch
)
