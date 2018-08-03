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
	echo "arch_cc_version = \"3.9\"" >> out/args.gn
	echo "host_cc_version = \"3.9\"" >> out/args.gn
else
	# Local
	echo "Testing kokoro build locally..."
	make out/args.gn
fi

# TODO: Kokoro is missing ninja, gcc-4.9 or above and qemu
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
