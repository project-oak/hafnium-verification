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

"""Parse Repo manifest and symlink files specified in <linkfile> tags.

This is a workaround for Kokoro which does not support <linkfile>.
"""

import argparse
import os
import sys
import xml.etree.ElementTree as ET

def main():
	parser = argparse.ArgumentParser()
	parser.add_argument("root_dir", help="root directory")
	args = parser.parse_args()

	manifest = os.path.join(args.root_dir, ".repo", "manifest.xml")
	tree = ET.parse(manifest)
	root = tree.getroot()
	assert(root.tag == "manifest");

	for proj in root:
		if proj.tag != "project":
			continue

		proj_name = proj.attrib["name"]
		proj_path = proj.attrib["path"]

		for linkfile in proj:
			if linkfile.tag != "linkfile":
				continue

			linkfile_src = linkfile.attrib["src"]
			linkfile_dest = linkfile.attrib["dest"]
			src_path = os.path.join(
				args.root_dir, proj_path, linkfile_src)
			dest_path = os.path.join(args.root_dir, linkfile_dest)

			os.symlink(src_path, dest_path)

if __name__ == "__main__":
    sys.exit(main())
