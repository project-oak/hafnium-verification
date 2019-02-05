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

"""Runs make to build a target."""

import argparse
import os
import shutil
import subprocess
import sys


def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", required=True)
    parser.add_argument("--out_file", required=True)
    parser.add_argument("--copy_out_file", required=True)
    args, make_args = parser.parse_known_args()

    os.chdir(args.directory)
    os.environ["PWD"] = args.directory
    status = subprocess.call(["make"] + make_args)
    if status != 0:
        return status

    shutil.copyfile(args.out_file, args.copy_out_file)
    return 0


if __name__ == "__main__":
    sys.exit(Main())
