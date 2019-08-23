#!/usr/bin/env python
#
# Copyright 2019 The Hafnium Authors.
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

"""Wrapper around Device Tree Compiler (dtc)"""

import argparse
import os
import subprocess
import sys

DTC = "dtc"

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input-file")
    parser.add_argument("-o", "--output-file")
    args = parser.parse_args()

    dtc_args = [
            DTC,
            "-I", "dts", "-O", "dtb",
            "--out-version", "17",
        ]

    if args.output_file:
        dtc_args += [ "-o", args.output_file ]
    if args.input_file:
        dtc_args += [ args.input_file ]

    return subprocess.call(dtc_args)

if __name__ == "__main__":
    sys.exit(main())
