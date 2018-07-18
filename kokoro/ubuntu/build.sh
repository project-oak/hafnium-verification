#!/bin/bash

# Fail on any error.
set -e
# # Display commands being run.
set -x

cd git/hafnium
CLANG="clang-3.9" make
