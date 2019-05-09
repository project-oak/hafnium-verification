#!/usr/bin/env python
#
# Copyright 2018 The Hafnium Authors.
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

HFTEST_LOG_PREFIX = "[hftest] "
HFTEST_LOG_FAILURE_PREFIX = "Failure:"
HFTEST_LOG_FINISHED = "FINISHED"


def log_timeout_returncode(f, returncode):
    if returncode == 0:
        return
    elif returncode == 124:
        f.write("\r\n{}{} timed out\r\n".format(HFTEST_LOG_PREFIX,
                                                HFTEST_LOG_FAILURE_PREFIX))
    else:
        f.write("\r\n{}{} process return code {}\r\n".format(
            HFTEST_LOG_PREFIX, HFTEST_LOG_FAILURE_PREFIX, returncode))


def qemu(image, initrd, args, log):
    qemu_args = [
        "timeout", "--foreground", "10s",
        "./prebuilts/linux-x64/qemu/qemu-system-aarch64", "-M", "virt,gic_version=3",
        "-cpu", "cortex-a57", "-smp", "4", "-m", "64M", "-machine", "virtualization=true",
        "-nographic", "-nodefaults", "-serial", "stdio", "-kernel", image,
    ]
    if initrd:
        qemu_args += ["-initrd", initrd]
    if args:
        qemu_args += ["-append", args]
    # Save the log to a file.
    with open(log, "w") as f:
        f.write("$ {}\r\n".format(" ".join(qemu_args)))
        f.flush()
        try:
            subprocess.check_call(qemu_args, stdout=f, stderr=f)
        except subprocess.CalledProcessError as e:
            log_timeout_returncode(f, e.returncode)
    # Return that log for processing.
    with open(log, "r") as f:
        return f.read()


def fvp(image, initrd, args, log):
    uart0_log = log + ".uart0"
    uart1_log = log + ".uart1"
    fdt = log + ".dtb"
    dtc_args = [
        "dtc", "-I", "dts", "-O", "dtb",
        "-o", fdt,
    ]
    fvp_args = [
        "timeout", "--foreground", "40s",
        "../fvp/Base_RevC_AEMv8A_pkg/models/Linux64_GCC-4.9/FVP_Base_RevC-2xAEMv8A",
        "-C", "pctl.startup=0.0.0.0",
        "-C", "bp.secure_memory=0",
        "-C", "cluster0.NUM_CORES=4",
        "-C", "cluster1.NUM_CORES=4",
        "-C", "cache_state_modelled=0",
        "-C", "bp.vis.disable_visualisation=true",
        "-C", "bp.vis.rate_limit-enable=false",
        "-C", "bp.terminal_0.start_telnet=false",
        "-C", "bp.terminal_1.start_telnet=false",
        "-C", "bp.terminal_2.start_telnet=false",
        "-C", "bp.terminal_3.start_telnet=false",
        "-C", "bp.pl011_uart0.untimed_fifos=1",
        "-C", "bp.pl011_uart0.unbuffered_output=1",
        "-C", "bp.pl011_uart0.out_file=" + uart0_log,
        "-C", "bp.pl011_uart1.out_file=" + uart1_log,
        "-C", "cluster0.cpu0.RVBAR=0x04020000",
        "-C", "cluster0.cpu1.RVBAR=0x04020000",
        "-C", "cluster0.cpu2.RVBAR=0x04020000",
        "-C", "cluster0.cpu3.RVBAR=0x04020000",
        "-C", "cluster1.cpu0.RVBAR=0x04020000",
        "-C", "cluster1.cpu1.RVBAR=0x04020000",
        "-C", "cluster1.cpu2.RVBAR=0x04020000",
        "-C", "cluster1.cpu3.RVBAR=0x04020000",
        "--data", "cluster0.cpu0=prebuilts/linux-aarch64/arm-trusted-firmware/bl31.bin@0x04020000",
        "--data", "cluster0.cpu0=" + fdt + "@0x82000000",
        "--data", "cluster0.cpu0=" + image + "@0x80000000",
        "-C", "bp.ve_sysregs.mmbSiteDefault=0",
        "-C", "bp.ve_sysregs.exit_on_shutdown=1",
    ]
    initrd_start = 0x84000000
    initrd_end = 0x85000000  # Default value
    if initrd:
        fvp_args += ["--data", "cluster0.cpu0={}@{}".format(initrd, hex(initrd_start))]
        initrd_end = initrd_start + os.path.getsize(initrd)


    with open(log, "w") as f:
        f.write("$ {}\r\n".format(" ".join(dtc_args)))
        f.flush()
        dtc = subprocess.Popen(
            dtc_args, stdout=f, stderr=f, stdin=subprocess.PIPE)
        with open(
                "prebuilts/linux-aarch64/arm-trusted-firmware/fvp-base-gicv3-psci-1t.dts",
                "r") as base_dts:
            dtc.stdin.write(base_dts.read())
        dtc.stdin.write("/ {\n")
        dtc.stdin.write("        chosen {\n")
        dtc.stdin.write("                bootargs = \"" + args + "\";\n")
        dtc.stdin.write("                stdout-path = \"serial0:115200n8\";\n")
        dtc.stdin.write("                linux,initrd-start = <{}>;\n".format(initrd_start))
        dtc.stdin.write("                linux,initrd-end = <{}>;\n".format(initrd_end))
        dtc.stdin.write("        };\n")
        dtc.stdin.write("};\n")
        dtc.stdin.close()
        dtc.wait()

        f.write("$ {}\r\n".format(" ".join(fvp_args)))
        f.flush()
        returncode = subprocess.call(fvp_args, stdout=f, stderr=f)
        with open(uart0_log, "r") as g:
            f.write(g.read())
        log_timeout_returncode(f, returncode)

    with open(log, "r") as f:
        return f.read()


def emulator(use_fvp, image, initrd, args, log):
    if use_fvp:
        return fvp(image, initrd, args, log)
    else:
        return qemu(image, initrd, args, log)


def ensure_dir(path):
    try:
        os.makedirs(path)
    except OSError:
        if not os.path.isdir(path):
            raise


def hftest_lines(raw):
    return [
        line[len(HFTEST_LOG_PREFIX):]
        for line in raw.splitlines()
        if line.startswith(HFTEST_LOG_PREFIX)
    ]


def Main():
    parser = argparse.ArgumentParser()
    parser.add_argument("image")
    parser.add_argument("--out", required=True)
    parser.add_argument("--log", required=True)
    parser.add_argument("--out_initrd")
    parser.add_argument("--initrd")
    parser.add_argument("--suite")
    parser.add_argument("--test")
    parser.add_argument("--vm_args")
    parser.add_argument("--fvp", type=bool)
    args = parser.parse_args()
    # Resolve some paths.
    image = os.path.join(args.out, args.image + ".bin")
    initrd = None
    suite = args.image
    if args.initrd:
        initrd = os.path.join(args.out_initrd, "obj", args.initrd, "initrd.img")
        suite += "_" + args.initrd
    vm_args = args.vm_args or ""
    log = os.path.join(args.log, suite)
    ensure_dir(log)
    print("Logs saved under", log)
    log_file = os.path.join(log, "sponge_log.log")
    with open(log_file, "w") as full_log:
        # Query the tests in the image.
        out = emulator(args.fvp, image, initrd, vm_args + " json",
                       os.path.join(log, "json.log"))
        full_log.write(out)
        full_log.write("\r\n\r\n")
        hftest_json = "\n".join(hftest_lines(out))
        tests = json.loads(hftest_json)
        # Run the selected tests.
        tests_run = 0
        failures = 0
        suite_re = re.compile(args.suite or ".*")
        test_re = re.compile(args.test or ".*")
        suites_xml = ET.Element("testsuites")
        suites_xml.set("name", suite)
        suites_xml.set(
            "timestamp",
            datetime.datetime.now().replace(microsecond=0).isoformat())
        for suite in tests["suites"]:
            if not suite_re.match(suite["name"]):
                continue
            tests_run_from_suite = 0
            failures_from_suite = 0
            suite_xml = ET.SubElement(suites_xml, "testsuite")
            suite_xml.set("name", suite["name"])
            for test in suite["tests"]:
                if not test_re.match(test):
                    continue
                test_xml = ET.SubElement(suite_xml, "testcase")
                test_xml.set("name", test)
                test_xml.set("classname", suite['name'])
                test_xml.set("status", "run")
                tests_run_from_suite += 1
                if tests_run_from_suite == 1:
                    print("    SUITE", suite["name"])
                print("      RUN", test)
                test_log = os.path.join(log,
                                        suite["name"] + "." + test + ".log")
                out = emulator(
                    args.fvp, image, initrd,
                    vm_args + " run {} {}".format(suite["name"], test),
                    test_log)
                full_log.write(out)
                full_log.write("\r\n\r\n")
                hftest_out = hftest_lines(out)
                if len(
                        hftest_out
                ) > 0 and hftest_out[-1] == HFTEST_LOG_FINISHED and not any(
                        l.startswith(HFTEST_LOG_FAILURE_PREFIX)
                        for l in hftest_out):
                    print("        PASS")
                else:
                    failures_from_suite += 1
                    failure_xml = ET.SubElement(test_xml, "failure")
                    # TODO: set a meaningful message and put log in CDATA
                    failure_xml.set("message", "Test failed")
                    print("[x]     FAIL --", test_log)
            tests_run += tests_run_from_suite
            failures += failures_from_suite
            suite_xml.set("tests", str(tests_run_from_suite))
            suite_xml.set("failures", str(failures_from_suite))
    suites_xml.set("tests", str(tests_run))
    suites_xml.set("failures", str(failures))
    with open(os.path.join(log, "sponge_log.xml"), "w") as f:
        ET.ElementTree(suites_xml).write(
            f, encoding='utf-8', xml_declaration=True)
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
