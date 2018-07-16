#!/usr/bin/env python

"""Extract embedded offsets from an object file.

We let the compiler calculate the offsets it is going to use and have those
emitted into and object file. This is the next pass which extracts those offsets
and stores them in a header file for the assembly to include and use.
"""

import argparse
import os
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
      "{}objdump".format(args.tool_prefix),
      "--disassemble-all",
      "--section",
      ".rodata",
      args.input])
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
