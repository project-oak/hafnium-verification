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

"""Check ELF file for assembly-level regressions.

Objdumps the given ELF file and detects known assembly patterns, checking for
regressions on bugs such as CPU erratas. Throws an exception if a broken pattern
is detected.
"""

import argparse
import os
import re
import subprocess
import sys

HF_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
CLANG_ROOT = os.path.join(HF_ROOT, "prebuilts", "linux-x64", "clang")
OBJDUMP = os.path.join(CLANG_ROOT, "bin", "llvm-objdump")
NM = os.path.join(CLANG_ROOT, "bin", "llvm-nm")

def check_eret_speculation_barrier(args):
	"""
	Some ARM64 CPUs speculatively execute instructions after ERET.
	Check that every ERET is followed by DSB NSH and ISB.
	"""

	objdump_stdout = subprocess\
		.check_output([ OBJDUMP, "-d", args.input_elf ])\
		.decode("utf-8")\
		.splitlines()

	found_eret = False

	STATE_DEFAULT = 1
	STATE_EXPECT_DSB_NSH = 2
	STATE_EXPECT_ISB = 3

	REGEX_ERET = re.compile(r"^\s*[0-9a-f]+:\s*e0 03 9f d6\s+eret$")
	REGEX_DSB_NSH = re.compile(r"^\s*[0-9a-f]+:\s*9f 37 03 d5\s*dsb\s+nsh$")
	REGEX_ISB = re.compile(r"^\s*[0-9a-f]+:\s*df 3f 03 d5\s+isb$")

	state = STATE_DEFAULT
	for line in objdump_stdout:
		if state == STATE_DEFAULT:
			if re.match(REGEX_ERET, line):
				found_eret = True
				state = STATE_EXPECT_DSB_NSH
		elif state == STATE_EXPECT_DSB_NSH:
			if re.match(REGEX_DSB_NSH, line):
				state = STATE_EXPECT_ISB
			else:
				raise Exception("ERET not followed by DSB NSH")
		elif state == STATE_EXPECT_ISB:
			if re.match(REGEX_ISB, line):
				state = STATE_DEFAULT
			else:
				raise Exception("ERET not followed by ISB")

	# Ensure that at least one instance was found, otherwise the regexes are
	# probably wrong.
	if not found_eret:
		raise Exception("Could not find any ERET instructions")

def check_max_image_size(args):
	"""
	Check that the ELF's effective image size does not exceed maximum
	allowed image size, if specified in command-line arguments.
	"""

	if args.max_image_size <= 0:
		return

	nm_stdout = subprocess\
		.check_output([ NM, args.input_elf ])\
		.decode("utf-8")\
		.splitlines()

	COLUMN_COUNT = 3
	COLUMN_IDX_VALUE = 0
	COLUMN_IDX_TYPE = 1
	COLUMN_IDX_NAME = 2

	image_size = None
	for line in nm_stdout:
		line = line.split()
		if len(line) != COLUMN_COUNT:
			raise Exception(
				"Unexpected number of columns in NM output")

		if line[COLUMN_IDX_NAME] == "image_size":
			if line[COLUMN_IDX_TYPE] != "A":
				raise Exception(
					"Unexpected type of image_size symbol")
			image_size = int(line[COLUMN_IDX_VALUE], 16)
			break

	if image_size is None:
		raise Exception("Could not find value of image_size symbol")
	elif image_size > args.max_image_size:
		raise Exception(
			"Image size exceeds maximum allowed image size " +
			"({}B > {}B)".format(image_size, args.max_image_size))

def Main():
	parser = argparse.ArgumentParser()
	parser.add_argument("input_elf",
		help="ELF file to analyze")
	parser.add_argument("stamp_file",
		help="file to be touched if successful")
	parser.add_argument("--max-image-size",
		required=False, type=int, default=0,
		help="maximum allowed image size in bytes")
	args = parser.parse_args()

	check_eret_speculation_barrier(args)
	check_max_image_size(args)

	# Touch `stamp_file`.
	with open(args.stamp_file, "w"):
		pass

	return 0

if __name__ == "__main__":
	sys.exit(Main())
