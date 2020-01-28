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

source "$(dirname ${BASH_SOURCE[0]})/../build/bash/common.inc"

# Initialize global variables, prepare repo for building.
init_build

# Assign default values to variables.
if is_kokoro_build
then
	# Default config for Kokoro builds.
	default_value HAFNIUM_HERMETIC_BUILD true
	default_value HAFNIUM_SKIP_LONG_RUNNING_TESTS false
	default_value HAFNIUM_RUN_ALL_QEMU_CPUS true
else
	# Default config for local builds.
	default_value HAFNIUM_HERMETIC_BUILD false
	default_value HAFNIUM_SKIP_LONG_RUNNING_TESTS true
	default_value HAFNIUM_RUN_ALL_QEMU_CPUS false
fi

# If HAFNIUM_HERMETIC_BUILD is "true", relaunch this script inside a container.
# The 'run_in_container.sh' script will set the variable value to 'inside' to
# avoid recursion.
if [ "${HAFNIUM_HERMETIC_BUILD}" == "true" ]
then
	exec "${ROOT_DIR}/build/run_in_container.sh" "$(get_script_path)" $@
fi

USE_FVP=false

while test $# -gt 0
do
	case "$1" in
	--fvp)
		USE_FVP=true
		;;
	--skip-long-running-tests)
		HAFNIUM_SKIP_LONG_RUNNING_TESTS=true
		;;
	--run-all-qemu-cpus)
		HAFNIUM_RUN_ALL_QEMU_CPUS=true
		;;
	*)
		echo "Unexpected argument $1"
		exit 1
		;;
	esac
	shift
done

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

for proj in $(cd project/ && ls)
do
  make PROJECT=${proj}
done

#
# Step 2: make sure it works.
#

TEST_ARGS=()
if [ $USE_FVP == true ]
then
	TEST_ARGS+=(--fvp)
fi
if [ "${HAFNIUM_SKIP_LONG_RUNNING_TESTS}" == "true" ]
then
	TEST_ARGS+=(--skip-long-running-tests)
fi
if [ "${HAFNIUM_RUN_ALL_QEMU_CPUS}" == "true" ]
then
	TEST_ARGS+=(--run-all-qemu-cpus)
fi
./kokoro/test.sh ${TEST_ARGS[@]}

#
# Step 3: static analysis.
#

make check
if is_repo_dirty
then
	echo "Run \`make check\' locally to fix this."
	exit 1
fi

#
# Step 4: make sure the code looks good.
#

make format
if is_repo_dirty
then
	echo "Run \`make format\' locally to fix this."
	exit 1
fi

make checkpatch

#
# Step 5: make sure there's not lint.
#

make tidy
if is_repo_dirty
then
	echo "Run \`make tidy\' locally to fix this."
	exit 1
fi

#
# Step 6: make sure all the files have a license.
#

make license
if is_repo_dirty
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
make HAFNIUM_PATH="${ROOT_DIR}" checkpatch
)
