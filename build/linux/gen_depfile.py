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
"""Generate a depfile for a folder."""

import argparse
import os
import sys

def main():
	parser = argparse.ArgumentParser()
	parser.add_argument("root_dir", help="input directory")
	parser.add_argument("stamp_file", help="stamp file to be touched")
	parser.add_argument("dep_file", help="depfile to be written")
	args = parser.parse_args()

	# Compile list of all files in the folder, relative to `root_dir`.
	sources = []
	for root, _, files in os.walk(args.root_dir):
		sources.extend([ os.path.join(root, f) for f in files ])
	sources = sorted(sources)

	# Write `dep_file` as a Makefile rule for `stamp_file`.
	with open(args.dep_file, "w") as f:
		f.write(args.stamp_file)
		f.write(":")
		for source in sources:
			f.write(' ');
			f.write(source)
		f.write(os.linesep)

	# Touch `stamp_file`.
	with open(args.stamp_file, "w"):
		pass

if __name__ == "__main__":
    sys.exit(main())
