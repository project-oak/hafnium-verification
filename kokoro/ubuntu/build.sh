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

#
# Step 1: make sure it builds.
#

export ARCH=aarch64
export PLATFORM=qemu

# TODO: add a gcc-4.9 or above prebuilt to check the gcc build too?
# Check the build works.
make
make check

#
# Step 2: make sure it works.
#

./kokoro/ubuntu/test.sh

#
# Step 3: make sure the code looks good.
#

make format
make tidy
make license

if [[ `git status --porcelain` ]]
then
	echo "Run \`make format\', \`make tidy\` and \`make license\` locally to fix this."
	exit 1
fi
