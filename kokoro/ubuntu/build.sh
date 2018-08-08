#!/bin/bash

# Fail on any error.
set -e
# Display commands being run.
set -x

# Detect server vs local run. Local run should be from the project's root
# directory.
if [ -v KOKORO_JOB_NAME ]
then
	# Server
	cd git/hafnium
	make out/args.gn
else
	# Local
	echo "Testing kokoro build locally..."
	make out/args.gn
fi

#
# Step 1: make sure it builds.
#

# TODO: add a gcc-4.9 or above prebuilt to check the gcc build too?
# Check the build works.
make
#TODO: static analysis with make check

#
# Step 2: make sure it works.
#

./kokoro/ubuntu/test.sh

#
# Step 3: make sure the code looks good.
#

make format
make tidy

if [[ `git status --porcelain` ]]
then
	echo "Run `make format` and `make tidy` locally to fix this."
	exit 1
fi
