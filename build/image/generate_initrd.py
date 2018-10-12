#!/usr/bin/env python
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
    parser.add_argument("--primary_vm", required=True)
    parser.add_argument("--primary_vm_initrd")
    parser.add_argument(
        "--secondary_vm",
        action="append",
        nargs=4,
        metavar=("MEMORY", "CORES", "NAME", "IMAGE"))
    parser.add_argument("--staging", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    # Prepare the primary VM image.
    staged_files = ["vmlinuz"]
    shutil.copyfile(args.primary_vm, os.path.join(args.staging, "vmlinuz"))
    # Prepare the primary VM's initrd. Currently, it just makes an empty one.
    if args.primary_vm_initrd:
        raise NotImplementedError(
            "This doesn't copy the primary VM's initrd yet")
    with open(os.path.join(args.staging, "initrd.img"), "w") as vms_txt:
        staged_files.append("initrd.img")
    # Prepare the secondary VMs.
    with open(os.path.join(args.staging, "vms.txt"), "w") as vms_txt:
        staged_files.append("vms.txt")
        if args.secondary_vm:
            for vm in args.secondary_vm:
                (vm_memory, vm_cores, vm_name, vm_image) = vm
                staged_files.append(vm_name)
                shutil.copy(vm_image, os.path.join(args.staging, vm_name))
                vms_txt.write("{} {} {}\n".format(vm_memory, vm_cores, vm_name))
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
