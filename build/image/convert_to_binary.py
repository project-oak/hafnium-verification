#!/usr/bin/env python
"""Convert a file to binary format.

Calls objcopy to convert a file into raw binary format.
"""

import argparse
import subprocess
import sys


def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tool_prefix", required=True)
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    subprocess.check_call([
        "{}objcopy".format(args.tool_prefix), "-O", "binary", args.input,
        args.output
    ])
    return 0


if __name__ == "__main__":
    sys.exit(Main())
