#!/usr/bin/env python3
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

"""Generate an initial RAM disk for a Linux VM."""

import argparse
import os
import shutil
import subprocess
import sys

def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--staging", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    # Package files into an initial RAM disk.
    with open(args.output, "w") as initrd:
        # Move into the staging directory so the file names taken by cpio don't
        # include the path.
        os.chdir(args.staging)
        staged_files = [os.path.join(root, filename)
          for (root, dirs, files) in os.walk(".") for filename in files + dirs]
        cpio = subprocess.Popen(
            ["cpio", "--create", "--format=newc"],
            stdin=subprocess.PIPE,
            stdout=initrd,
            stderr=subprocess.PIPE)
        cpio.communicate(input="\n".join(staged_files).encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(Main())
