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

"""Add license header to source files.

If the file doesn't have the license header, add it with the appropriate comment
style.
"""

import argparse
import datetime
import re
import sys


apache2 = """{comment} Copyright {year} Google LLC
{comment}
{comment} Licensed under the Apache License, Version 2.0 (the "License");
{comment} you may not use this file except in compliance with the License.
{comment} You may obtain a copy of the License at
{comment}
{comment}     https://www.apache.org/licenses/LICENSE-2.0
{comment}
{comment} Unless required by applicable law or agreed to in writing, software
{comment} distributed under the License is distributed on an "AS IS" BASIS,
{comment} WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
{comment} See the License for the specific language governing permissions and
{comment} limitations under the License."""

def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("file")
    parser.add_argument("--style", choices=["c", "hash"], required=True)
    args = parser.parse_args()
    header = "/*\n" if args.style == "c" else ""
    year = str(datetime.datetime.now().year)
    header += apache2.format(comment=" *" if args.style == "c" else "#", year=year)
    header += "\n */" if args.style == "c" else ""
    header += "\n\n"
    header_regex = re.escape(header).replace(year, r"\d\d\d\d")
    with open(args.file, "r") as f:
        contents = f.read()
        if re.search(header_regex, contents):
            return
    with open(args.file, "w") as f:
        f.write(header)
        f.write(contents)

if __name__ == "__main__":
    sys.exit(Main())
