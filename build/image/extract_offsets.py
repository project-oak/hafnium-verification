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

"""Extract embedded offsets from an object file.

We let the compiler calculate the offsets it is going to use and have those
emitted into and object file. This is the next pass which extracts those offsets
and stores them in a header file for the assembly to include and use.
"""

import argparse
import re
import subprocess
import sys


def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tool_prefix", required=True)
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    raw = subprocess.check_output([
        "{}objdump".format(args.tool_prefix), "--disassemble-all", "--section",
        ".rodata", args.input
    ])
    lines = raw.split('\n')
    with open(args.output, 'w') as header:
        header.write('#pragma once\n\n')
        for n in range(len(lines)):
            # Find a defined offset
            match = re.match('.+DEFINE_OFFSET__([^>]+)', lines[n])
            if not match:
                continue
            name = match.group(1)
            # The next line tells the offset
            if "..." in lines[n + 1]:
                offset = 0
            else:
                offset = re.match('.+\.[\S]+\s+(.+)$', lines[n + 1]).group(1)
            # Write the offset to the header
            header.write("#define {} {}\n".format(name, offset))
    return 0


if __name__ == "__main__":
    sys.exit(Main())
