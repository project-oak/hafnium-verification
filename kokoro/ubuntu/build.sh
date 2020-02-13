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

SCRIPT_NAME="$(realpath "${BASH_SOURCE[0]}")"
ROOT_DIR="$(realpath $(dirname "${SCRIPT_NAME}")/../..)"

# Fail on any error.
set -e
# Fail on any part of a pipeline failing.
set -o pipefail
# Treat unset variables as an error.
set -u
# Display commands being run.
set -x

# Default value of HAFNIUM_HERMETIC_BUILD is "true" for Kokoro builds.
if [ -v KOKORO_JOB_NAME -a ! -v HAFNIUM_HERMETIC_BUILD ]
then
	HAFNIUM_HERMETIC_BUILD=true
fi

# If HAFNIUM_HERMETIC_BUILD is "true" (not default), relaunch this script inside
# a container. The 'run_in_container.sh' script will set the variable value to
# 'inside' to avoid recursion.
if [ "${HAFNIUM_HERMETIC_BUILD:-}" == "true" ]
then
	exec "${ROOT_DIR}/build/run_in_container.sh" ${SCRIPT_NAME} $@
fi

USE_FVP=0

while test $# -gt 0
do
  case "$1" in
    --fvp) USE_FVP=1
      ;;
    *) echo "Unexpected argument $1"
      exit 1
      ;;
  esac
  shift
done

# Detect server vs local run. Local run should be from the project's root
# directory.
if [ -v KOKORO_JOB_NAME ]
then
	# Server
	cd git/hafnium
fi

CLANG=${PWD}/prebuilts/linux-x64/clang/bin/clang

# Kokoro does something weird that makes all files look dirty to git diff-index;
# this fixes it so that the Linux build doesn't think it has a dirty tree for
# building the Hafnium kernel module (and so end up with a version magic string
# that doesn't match the prebuilt kernel).
(
	cd third_party/linux &&
	git status
)

#
# Step 1: make sure it builds.
#

# Check the hypervisor builds.
make

#
# Step 2: make sure it works.
#

if [ $USE_FVP == 1 ]
then
  ./kokoro/ubuntu/test.sh --fvp
else
  ./kokoro/ubuntu/test.sh
fi

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

# Step 7: make sure the Linux driver maintains style. It's already built as part
# of the tests.
(
export ARCH=arm64 &&
export CROSS_COMPILE=aarch64-linux-gnu- &&
cd driver/linux &&
make checkpatch
)
