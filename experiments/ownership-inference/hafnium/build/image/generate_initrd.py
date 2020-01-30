#!/usr/bin/env python3
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

"""Generate an initial RAM disk for the hypervisor.

Packages the VMs, initrds for the VMs and the list of secondary VMs (vms.txt)
into an initial RAM disk image.
"""

import argparse
import os
import shutil
import subprocess
import sys

def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--file",
        action="append", nargs=2,
        metavar=("NAME", "PATH"),
        help="File at host location PATH to be added to the RAM disk as NAME")
    parser.add_argument("-s", "--staging", required=True)
    parser.add_argument("-o", "--output", required=True)
    args = parser.parse_args()

    # Create staging folder if needed.
    if not os.path.isdir(args.staging):
        os.makedirs(args.staging)

    # Copy files into the staging folder.
    staged_files = []
    for name, path in args.file:
        shutil.copyfile(path, os.path.join(args.staging, name))
        assert name not in staged_files
        staged_files.append(name)

    # Package files into an initial RAM disk.
    with open(args.output, "w") as initrd:
        # Move into the staging directory so the file names taken by cpio don't
        # include the path.
        os.chdir(args.staging)
        cpio = subprocess.Popen(
            ["cpio", "--create"],
            stdin=subprocess.PIPE,
            stdout=initrd,
            stderr=subprocess.PIPE)
        cpio.communicate(input="\n".join(staged_files).encode("utf-8"))
    return 0

if __name__ == "__main__":
    sys.exit(Main())
