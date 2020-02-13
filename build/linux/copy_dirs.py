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

#!/usr/bin/env python
"""Copies all files inside one folder to another, preserving subfolders."""

import argparse
import os
import shutil
import sys

def main():
	parser = argparse.ArgumentParser()
	parser.add_argument("source_folder",
	                    help="directory to be copied from")
	parser.add_argument("destination_folder",
	                    help="directory to be copied into")
	parser.add_argument("stamp_file",
	                    help="stamp file to be touched")
	args = parser.parse_args()

	# Walk the subfolders of the source directory and copy individual files.
	# Not using shutil.copytree() because it never overwrites files.
	for root, _, files in os.walk(args.source_folder):
		for f in files:
			abs_src_path = os.path.join(root, f)
			rel_path = os.path.relpath(abs_src_path, args.source_folder)
			abs_dst_path = os.path.join(args.destination_folder, rel_path)
			abs_dst_folder = os.path.dirname(abs_dst_path)
			if not os.path.isdir(abs_dst_folder):
				os.makedirs(abs_dst_folder)
			shutil.copyfile(abs_src_path, abs_dst_path)

	# Touch `stamp_file`.
	with open(args.stamp_file, "w"):
		pass

if __name__ == "__main__":
    sys.exit(main())
