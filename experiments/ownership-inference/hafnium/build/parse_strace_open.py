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

"""Script which parses the output of `strace` and dumping a list of files
that were touched by the traced processes outside of whitelisted folders.
It assumes that strace was invoked with the following arguments:
    -e trace=%file,chdir,%process   record required syscalls
    -qq                             silence 'exit code' records
    -o <file>                       output format is different when writing
                                    to a file from printing to the console
"""

import argparse
import os
import sys

FORK_SYSCALLS = [
    "clone",
    "fork",
    "vfork",
    ]
OPEN_SYSCALLS = [
    "access",
    "creat",
    "lstat",
    "mkdir",
    "open",
    "openat",
    "readlink",
    "stat",
    ]

def get_unfinished(line):
    pos = line.find("<unfinished ...>")
    if pos < 0:
        return None
    else:
        return line[:pos]

def get_resumed(line):
    pos = line.find(" resumed>")
    if pos < 0:
        return None
    else:
        return line[pos + len(" resumed>"):]

def merge_unfinished_lines(lines):
    """Process input lines and merge those split by an interrupting syscall."""
    # Lines in the order they were started being written.
    finished = []

    # Pending unfinished lines. Map from PID to index in `finished`.
    cursor = {}

    for line in lines:
        pid = int(line.split()[0])

        resumed = get_resumed(line)
        if resumed is not None:
            assert(pid in cursor)
            unfinished = get_unfinished(resumed)
            if unfinished is not None:
                finished[cursor[pid]] += unfinished
            else:
                finished[cursor[pid]] += resumed
                del(cursor[pid])
        else:
            assert(pid not in cursor)
            unfinished = get_unfinished(line)
            if unfinished is not None:
                # Line is unfinished. Store its location to `cursor`.
                cursor[pid] = len(finished)
                finished += [ unfinished ]
            else:
                finished += [ line ]
    return finished

def abs_path(cwd, path):
    """If `path` is relative, resolve it against the current working directory.
       Also normalize the resulting path."""
    if path[0] != '/':
        path = os.path.join(cwd, path)
    path = os.path.abspath(path)
    # while '//' in path:
    #     path = path.replace('//', '/')
    path = os.path.realpath(path)
    return path

def get_touched_files(lines, orig_cwd):
    """Parse strace output and return all files that an open()-like syscall was
       called on."""
    files = set()

    # Map from PID to the current working directory.
    cwd = {}

    # Map from PID to executable name
    executable = {}

    # Map from PID to the PID of the process which forked it.
    fork_of = {}

    first_pid = True
    for line in lines:
        # Split line: <pid>  <syscall info>
        line = line.split()
        pid = int(line[0])
        syscall = " ".join(line[1:])

        # If seeing a PID for the first time, derive its working directory
        # from its parent.
        if pid not in cwd:
            if first_pid:
                # Very first line of strace output. Set working directory from
                # command line arguments (should match cwd of strace).
                first_pid = False
                cwd[pid] = orig_cwd
            else:
                # There should have been a fork/clone syscall which spawned this
                # process. Inherit its working directory.
                cwd[pid] = cwd[fork_of[pid]]

        # We are looking for lines which match:
        #   name(arg1, arg2, ..., argN) = result
        left_bracket = syscall.find("(")
        right_bracket = syscall.rfind(")")
        assign_sign = syscall.rfind("=")
        if left_bracket < 0 or right_bracket < 0 or assign_sign < right_bracket:
            continue

        syscall_name = syscall[:left_bracket]
        syscall_result = syscall[assign_sign+2:]

        syscall_args = syscall[left_bracket+1:right_bracket].split(",")
        syscall_args = list(map(lambda x: x.strip(), syscall_args))

        if syscall_name in FORK_SYSCALLS:
            # If this is a fork, keep track of the parent-child relationship.
            # The child's PID is the syscall's return code.
            new_pid = int(syscall_result)
            fork_of[new_pid] = pid
            executable[new_pid] = executable[pid]
        elif syscall_name == "chdir":
            # If this is a change of working directory, keep track of it.
            # It is in the first argument in quotes.
            new_dir = syscall_args[0][1:-1]
            cwd[pid] = abs_path(cwd[pid], new_dir)
        elif syscall_name == "execve":
            # If this is executing a new program, record its name.
            # It is in the first argument in quotes.
            binary_name = syscall_args[0][1:-1]
            executable[pid] = binary_name
        elif syscall_name in OPEN_SYSCALLS:
            # If this is a syscall touching a file, record the path.
            # We ignore the result code, i.e. record the path even if the
            # syscall failed to open it.
            arg_idx = 0
            if syscall_name == "openat":
                # openat() can open a file (second arg) relative to a given
                # folder (first arg). We only support passing AT_FDCWD, ie.
                # resolve against the current working directory.
                arg_idx = 1
                assert(syscall_args[0] == "AT_FDCWD")
            fname = abs_path(cwd[pid], syscall_args[arg_idx][1:-1])
            # Record the file and the name of the program which touched it.
            files.add((fname, executable[pid]))
    return files

def filter_results(files, root_dir):
    """Remove paths which are whitelisted from the results."""
    # Anything in the Hafnium directory is allowed.
    files = filter(lambda x: not x[0].startswith(root_dir + "/"), files)
    # Clang puts intermediate files in /tmp.
    files = filter(lambda x: not x[0].startswith("/tmp/"), files)
    return list(files)

def main(args):
    parser = argparse.ArgumentParser()
    parser.add_argument("root_dir",
                        help="Root directory of Hafnium, cwd of strace")
    args, make_args = parser.parse_known_args()

    stdin = map(lambda x: x.strip(), sys.stdin.readlines())
    stdin = merge_unfinished_lines(stdin)
    files = get_touched_files(stdin, args.root_dir)
    files = filter_results(files, args.root_dir)
    files = sorted(list(files))

    print("\n".join(map(lambda x: "{} ({})".format(x[0], x[1]), files)))

if __name__ == "__main__":
    main(sys.argv)
