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
	export CLANG="clang-3.9"
else
	# Local
	export CLANG=1
fi

# Check the build works
make

# # Check to code looks healthy, failing if any changes were made
# make format
# make tidy
#
# if [[ `git status --porcelain` ]]
# then
# 	exit 1
# fi
