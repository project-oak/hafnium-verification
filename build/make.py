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
    parser.add_argument("--copy_out_file", nargs=2,
                        help="Copy file after building. Takes two params: <src> <dest>")
    args, make_args = parser.parse_known_args()

    os.chdir(args.directory)
    os.environ["PWD"] = args.directory
    status = subprocess.call(["make"] + make_args)
    if status != 0:
        return status

    if args.copy_out_file is not None:
        shutil.copyfile(args.copy_out_file[0], args.copy_out_file[1])
    return 0


if __name__ == "__main__":
    sys.exit(Main())
