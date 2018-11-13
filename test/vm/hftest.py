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

"""Run tests.

Runs tests on QEMU.
"""

from __future__ import print_function

import xml.etree.ElementTree as ET

import argparse
import datetime
import json
import os
import re
import subprocess
import sys


def qemu(hafnium, initrd, args, log):
    qemu_args = [
        "timeout", "--foreground", "5s",
        "./prebuilts/linux-x64/qemu/qemu-system-aarch64", "-M", "virt,gic_version=3", "-cpu",
        "cortex-a57", "-m", "16M", "-machine", "virtualization=true",
        "-nographic", "-nodefaults", "-serial", "stdio", "-kernel", hafnium,
        "-initrd", initrd
    ]
    if args:
        qemu_args += ["-append", args]
    # Save the log to a file.
    with open(log, "w") as f:
        f.write("$ {}\r\n".format(" ".join(qemu_args)))
        f.flush()
        subprocess.check_call(qemu_args, stdout=f, stderr=f)
    # Return that log for processing.
    with open(log, "r") as f:
        return f.read()


def ensure_dir(path):
    try:
        os.makedirs(path)
    except OSError:
        if not os.path.isdir(path):
            raise


def hftest_lines(raw):
    prefix = "[hftest] "
    return [
        line[len(prefix):]
        for line in raw.splitlines()
        if line.startswith(prefix)
    ]


def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--log", required=True)
    parser.add_argument("--initrd", required=True)
    parser.add_argument("--suite")
    parser.add_argument("--test")
    args = parser.parse_args()
    # Resolve some paths.
    hafnium = os.path.join(args.out, "hafnium.bin")
    initrd = os.path.join(args.out, "initrd", args.initrd + ".img")
    log = os.path.join(args.log, args.initrd)
    ensure_dir(log)
    print("Logs saved under", log)
    log_file = os.path.join(log, "sponge_log.log")
    with open(log_file, "w") as sponge_log:
        # Query the tests in the image.
        out = qemu(hafnium, initrd, "json", os.path.join(log, "json.log"))
        sponge_log.write(out)
        sponge_log.write("\r\n\r\n")
        hftest_json = "\n".join(hftest_lines(out))
        tests = json.loads(hftest_json)
        # Run the selected tests.
        tests_run = 0
        failures = 0
        suite_re = re.compile(args.suite or ".*")
        test_re = re.compile(args.test or ".*")
        sponge = ET.Element("testsuites")
        sponge.set("name", args.initrd)
        sponge.set(
            "timestamp",
            datetime.datetime.now().replace(microsecond=0).isoformat())
        for suite in tests["suites"]:
            if not suite_re.match(suite["name"]):
                continue
            tests_run_from_suite = 0
            failures_from_suite = 0
            sponge_suite = ET.SubElement(sponge, "testsuite")
            sponge_suite.set("name", suite["name"])
            for test in suite["tests"]:
                if not test_re.match(test):
                    continue
                sponge_test = ET.SubElement(sponge_suite, "testcase")
                sponge_test.set("name", test)
                sponge_test.set("classname", suite['name'])
                sponge_test.set("status", "run")
                tests_run_from_suite += 1
                if tests_run_from_suite == 1:
                    print("    SUITE", suite["name"])
                print("      RUN", test)
                test_log = os.path.join(log,
                                        suite["name"] + "." + test + ".log")
                out = qemu(hafnium, initrd, "run {} {}".format(
                    suite["name"], test), test_log)
                sponge_log.write(out)
                sponge_log.write("\r\n\r\n")
                hftest_out = hftest_lines(out)
                if hftest_out[-1] == "PASS":
                    print("        PASS")
                else:
                    failures_from_suite += 1
                    sponge_failure = ET.SubElement(sponge_test, "failure")
                    # TODO: set a meaningful message and put log in CDATA
                    sponge_failure.set("message", "Test failed")
                    print("[x]     FAIL --", test_log)
            tests_run += tests_run_from_suite
            failures += failures_from_suite
            sponge_suite.set("tests", str(tests_run_from_suite))
            sponge_suite.set("failures", str(failures_from_suite))
    sponge.set("tests", str(tests_run))
    sponge.set("failures", str(failures))
    with open(os.path.join(log, "sponge_log.xml"), "w") as f:
        ET.ElementTree(sponge).write(f, encoding='utf-8', xml_declaration=True)
    # If none were run, this is probably a mistake.
    if tests_run == 0:
        print("Error: no tests match")
        return 10
    # Exit with 0 on success and 1 if any test failed.
    if failures:
        print("[x] FAIL:", failures, "of", tests_run, "tests failed")
        return 1
    else:
        print("    PASS: all", tests_run, "tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(Main())
