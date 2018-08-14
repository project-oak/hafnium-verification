#!/usr/bin/env python
"""Run tests.

Runs tests on QEMU.
"""

from __future__ import print_function

import argparse
import json
import os
import re
import subprocess
import sys


def qemu(hafnium, initrd, args, log):
    qemu_args = [
        "timeout", "--foreground", "5s",
        "./prebuilts/linux-x64/qemu/qemu-system-aarch64", "-M", "virt", "-cpu",
        "cortex-a57", "-m", "8M", "-machine", "virtualization=true",
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
    parser.add_argument("--initrd", required=True)
    parser.add_argument("--suite")
    parser.add_argument("--test")
    args = parser.parse_args()
    # Resolve some paths.
    hafnium = os.path.join(args.out, "hafnium.bin")
    initrd = os.path.join(args.out, "initrd", args.initrd + ".img")
    log = os.path.join(args.out, "test_log", args.initrd)
    ensure_dir(log)
    print("Logs saved under", log)
    # Query the tests in the image.
    out = qemu(hafnium, initrd, "json", os.path.join(log, "json.log"))
    hftest_json = "\n".join(hftest_lines(out))
    tests = json.loads(hftest_json)
    # Run the selected tests.
    tests_run = 0
    failures = 0
    suite_re = re.compile(args.suite or ".*")
    test_re = re.compile(args.test or ".*")
    for suite in tests['suites']:
        if not suite_re.match(suite['name']):
            continue
        tests_run_from_suite = 0
        for test in suite['tests']:
            if not test_re.match(test):
                continue
            tests_run_from_suite += 1
            if tests_run_from_suite == 1:
                print("    SUITE", suite['name'])
            print("      RUN", test)
            test_log = os.path.join(log, suite['name'] + "." + test + ".log")
            out = qemu(hafnium, initrd, "run {} {}".format(suite['name'], test), test_log)
            hftest_out = hftest_lines(out)
            if hftest_out[-1] == "PASS":
                print("        PASS")
            else:
                failures += 1
                print("[x]     FAIL --", test_log)
        tests_run += tests_run_from_suite
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
