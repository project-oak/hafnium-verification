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

"""Script which drives invocation of tests and parsing their output to produce
a results report.
"""

from __future__ import print_function

import xml.etree.ElementTree as ET

import argparse
import collections
import datetime
import json
import os
import re
import subprocess
import sys

HFTEST_LOG_PREFIX = "[hftest] "
HFTEST_LOG_FAILURE_PREFIX = "Failure:"
HFTEST_LOG_FINISHED = "FINISHED"

HF_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))
DTC_SCRIPT = os.path.join(HF_ROOT, "build", "image", "dtc.py")
FVP_BINARY = os.path.join(
    os.path.dirname(HF_ROOT), "fvp", "Base_RevC_AEMv8A_pkg", "models",
    "Linux64_GCC-4.9", "FVP_Base_RevC-2xAEMv8A")
FVP_PREBUILT_DTS = os.path.join(
    HF_ROOT, "prebuilts", "linux-aarch64", "arm-trusted-firmware",
    "fvp-base-gicv3-psci-1t.dts")

def read_file(path):
    with open(path, "r") as f:
        return f.read()

def write_file(path, to_write, append=False):
    with open(path, "a" if append else "w") as f:
        f.write(to_write)

def append_file(path, to_write):
    write_file(path, to_write, append=True)

def join_if_not_None(*args):
    return " ".join(filter(lambda x: x, args))

class ArtifactsManager:
    """Class which manages folder with test artifacts."""

    def __init__(self, log_dir):
        self.created_files = []
        self.log_dir = log_dir

        # Create directory.
        try:
            os.makedirs(self.log_dir)
        except OSError:
            if not os.path.isdir(self.log_dir):
                raise
        print("Logs saved under", log_dir)

        # Create files expected by the Sponge test result parser.
        self.sponge_log_path = self.create_file("sponge_log", ".log")
        self.sponge_xml_path = self.create_file("sponge_log", ".xml")

    def create_file(self, basename, extension):
        """Create and touch a new file in the log folder. Ensure that no other
        file of the same name was created by this instance of ArtifactsManager.
        """
        # Determine the path of the file.
        path = os.path.join(self.log_dir, basename + extension)

        # Check that the path is unique.
        assert(path not in self.created_files)
        self.created_files += [ path ]

        # Touch file.
        with open(path, "w") as f:
            pass

        return path


# Tuple holding the arguments common to all driver constructors.
# This is to avoid having to pass arguments from subclasses to superclasses.
DriverArgs = collections.namedtuple("DriverArgs", [
        "artifacts",
        "kernel",
        "initrd",
        "vm_args",
    ])


# State shared between the common Driver class and its subclasses during
# a single invocation of the target platform.
DriverRunState = collections.namedtuple("DriverRunState", [
        "log_path",
    ])


class Driver:
    """Parent class of drivers for all testable platforms."""

    def __init__(self, args):
        self.args = args

    def start_run(self, run_name):
        """Hook called by Driver subclasses before they invoke the target
        platform."""
        return DriverRunState(self.args.artifacts.create_file(run_name, ".log"))

    def exec_logged(self, run_state, exec_args):
        """Run a subprocess on behalf of a Driver subclass and append its
        stdout and stderr to the main log."""
        with open(run_state.log_path, "a") as f:
            f.write("$ {}\r\n".format(" ".join(exec_args)))
            f.flush()
            return subprocess.call(exec_args, stdout=f, stderr=f)

    def finish_run(self, run_state, ret_code):
        """Hook called by Driver subclasses after they finished running the
        target platform. `ret_code` argument is the return code of the main
        command run by the driver. A corresponding log message is printed."""
        # Decode return code and add a message to the log.
        with open(run_state.log_path, "a") as f:
            if ret_code == 124:
                f.write("\r\n{}{} timed out\r\n".format(
                    HFTEST_LOG_PREFIX, HFTEST_LOG_FAILURE_PREFIX))
            elif ret_code != 0:
                f.write("\r\n{}{} process return code {}\r\n".format(
                    HFTEST_LOG_PREFIX, HFTEST_LOG_FAILURE_PREFIX, ret_code))

        # Append log of this run to full test log.
        log_content = read_file(run_state.log_path)
        append_file(
            self.args.artifacts.sponge_log_path,
            log_content + "\r\n\r\n")
        return log_content


class QemuDriver(Driver):
    """Driver which runs tests in QEMU."""

    def __init__(self, args):
        Driver.__init__(self, args)

    def gen_exec_args(self, test_args):
        """Generate command line arguments for QEMU."""
        exec_args = [
            "timeout", "--foreground", "10s",
            "./prebuilts/linux-x64/qemu/qemu-system-aarch64",
            "-M", "virt,gic_version=3",
            "-cpu", "cortex-a57", "-smp", "4", "-m", "64M",
            "-machine", "virtualization=true",
            "-nographic", "-nodefaults", "-serial", "stdio",
            "-kernel", self.args.kernel,
        ]

        if self.args.initrd:
            exec_args += ["-initrd", self.args.initrd]

        vm_args = join_if_not_None(self.args.vm_args, test_args)
        if vm_args:
            exec_args += ["-append", vm_args]

        return exec_args

    def run(self, run_name, test_args):
        """Run test given by `test_args` in QEMU."""
        run_state = self.start_run(run_name)
        ret_code = self.exec_logged(run_state, self.gen_exec_args(test_args))
        return self.finish_run(run_state, ret_code)


class FvpDriver(Driver):
    """Driver which runs tests in ARM FVP emulator."""

    def __init__(self, args):
        Driver.__init__(self, args)

    def gen_dts(self, dts_path, test_args, initrd_start, initrd_end):
        """Create a DeviceTree source which will be compiled into a DTB and
        passed to FVP for a test run."""
        vm_args = join_if_not_None(self.args.vm_args, test_args)
        write_file(dts_path, read_file(FVP_PREBUILT_DTS))
        append_file(dts_path, """
                / {{
                    chosen {{
                        bootargs = "{}";
                        stdout-path = "serial0:115200n8";
                        linux,initrd-start = <{}>;
                        linux,initrd-end = <{}>;
                    }};
                }};
            """.format(vm_args, initrd_start, initrd_end))

    def gen_fvp_args(
            self, initrd_start, uart0_log_path, uart1_log_path, dtb_path):
        """Generate command line arguments for FVP."""
        fvp_args = [
            "timeout", "--foreground", "40s",
            FVP_BINARY,
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
            "-C", "bp.pl011_uart0.out_file=" + uart0_log_path,
            "-C", "bp.pl011_uart1.out_file=" + uart1_log_path,
            "-C", "cluster0.cpu0.RVBAR=0x04020000",
            "-C", "cluster0.cpu1.RVBAR=0x04020000",
            "-C", "cluster0.cpu2.RVBAR=0x04020000",
            "-C", "cluster0.cpu3.RVBAR=0x04020000",
            "-C", "cluster1.cpu0.RVBAR=0x04020000",
            "-C", "cluster1.cpu1.RVBAR=0x04020000",
            "-C", "cluster1.cpu2.RVBAR=0x04020000",
            "-C", "cluster1.cpu3.RVBAR=0x04020000",
            "--data", "cluster0.cpu0=prebuilts/linux-aarch64/arm-trusted-firmware/bl31.bin@0x04020000",
            "--data", "cluster0.cpu0=" + dtb_path + "@0x82000000",
            "--data", "cluster0.cpu0=" + self.args.kernel + "@0x80000000",
            "-C", "bp.ve_sysregs.mmbSiteDefault=0",
            "-C", "bp.ve_sysregs.exit_on_shutdown=1",
        ]

        if self.args.initrd:
            fvp_args += [
                "--data",
                "cluster0.cpu0={}@{}".format(
                    self.args.initrd, hex(initrd_start))
            ]

        return fvp_args

    def run(self, run_name, test_args):
        run_state = self.start_run(run_name)

        dts_path = self.args.artifacts.create_file(run_name, ".dts")
        dtb_path = self.args.artifacts.create_file(run_name, ".dtb")
        uart0_log_path = self.args.artifacts.create_file(run_name, ".uart0.log")
        uart1_log_path = self.args.artifacts.create_file(run_name, ".uart1.log")

        initrd_start = 0x84000000
        if self.args.initrd:
            initrd_end = initrd_start + os.path.getsize(self.args.initrd)
        else:
            initrd_end = 0x85000000  # Default value

        # Create a FDT to pass to FVP.
        self.gen_dts(dts_path, test_args, initrd_start, initrd_end)
        dtc_args = [ DTC_SCRIPT, "-i", dts_path, "-o", dtb_path ]
        self.exec_logged(run_state, dtc_args)

        # Run FVP.
        fvp_args = self.gen_fvp_args(
            initrd_start, uart0_log_path, uart1_log_path, dtb_path)
        ret_code = self.exec_logged(run_state, fvp_args)

        # Append UART0 output to main log.
        append_file(run_state.log_path, read_file(uart0_log_path))

        return self.finish_run(run_state, ret_code)


# Tuple used to return information about the results of running a set of tests.
TestRunnerResult = collections.namedtuple("TestRunnerResult", [
        "tests_run",
        "tests_failed",
    ])


class TestRunner:
    """Class which communicates with a test platform to obtain a list of
    available tests and driving their execution."""

    def __init__(self, artifacts, driver, image_name, suite_regex, test_regex):
        self.artifacts = artifacts
        self.driver = driver
        self.image_name = image_name

        self.suite_re = re.compile(suite_regex or ".*")
        self.test_re = re.compile(test_regex or ".*")

    def extract_hftest_lines(self, raw):
        """Extract hftest-specific lines from a raw output from an invocation
        of the test platform."""
        lines = []
        for line in raw.splitlines():
            if line.startswith("VM "):
                line = line[len("VM 0: "):]
            if line.startswith(HFTEST_LOG_PREFIX):
                lines.append(line[len(HFTEST_LOG_PREFIX):])
        return lines

    def get_test_json(self):
        """Invoke the test platform and request a JSON of available test and
        test suites."""
        out = self.driver.run("json", "json")
        hf_out = "\n".join(self.extract_hftest_lines(out))
        try:
            return json.loads(hf_out)
        except ValueError as e:
            print(out)
            raise e

    def collect_results(self, fn, it, xml_node):
        """Run `fn` on every entry in `it` and collect their TestRunnerResults.
        Insert "tests" and "failures" nodes to `xml_node`."""
        tests_run = 0
        tests_failed = 0
        for i in it:
            sub_result = fn(i)
            assert(sub_result.tests_run >= sub_result.tests_failed)
            tests_run += sub_result.tests_run
            tests_failed += sub_result.tests_failed

        xml_node.set("tests", str(tests_run))
        xml_node.set("failures", str(tests_failed))
        return TestRunnerResult(tests_run, tests_failed)

    def is_passed_test(self, test_out):
        """Parse the output of a test and return True if it passed."""
        return \
            len(test_out) > 0 and \
            test_out[-1] == HFTEST_LOG_FINISHED and \
            not any(l.startswith(HFTEST_LOG_FAILURE_PREFIX) for l in test_out)

    def run_test(self, suite, test, suite_xml):
        """Invoke the test platform and request to run a given `test` in given
        `suite`. Create a new XML node with results under `suite_xml`.
        Test only invoked if it matches the regex given to constructor."""
        if not self.test_re.match(test):
            return TestRunnerResult(tests_run=0, tests_failed=0)

        print("      RUN", test)
        log_name = suite["name"] + "." + test

        test_xml = ET.SubElement(suite_xml, "testcase")
        test_xml.set("name", test)
        test_xml.set("classname", suite['name'])
        test_xml.set("status", "run")

        out = self.extract_hftest_lines(self.driver.run(
            log_name, "run {} {}".format(suite["name"], test)))

        if self.is_passed_test(out):
            print("        PASS")
            return TestRunnerResult(tests_run=1, tests_failed=0)
        else:
            print("[x]     FAIL --", self.driver.file_path(log_name))
            failure_xml = ET.SubElement(test_xml, "failure")
            # TODO: set a meaningful message and put log in CDATA
            failure_xml.set("message", "Test failed")
            return TestRunnerResult(tests_run=1, tests_failed=1)

    def run_suite(self, suite, xml):
        """Invoke the test platform and request to run all matching tests in
        `suite`. Create new XML nodes with results under `xml`.
        Suite skipped if it does not match the regex given to constructor."""
        if not self.suite_re.match(suite["name"]):
            return TestRunnerResult(tests_run=0, tests_failed=0)

        print("    SUITE", suite["name"])
        suite_xml = ET.SubElement(xml, "testsuite")
        suite_xml.set("name", suite["name"])

        return self.collect_results(
            lambda test: self.run_test(suite, test, suite_xml),
            suite["tests"],
            suite_xml)

    def run_tests(self):
        """Run all suites and tests matching regexes given to constructor.
        Write results to sponge log XML. Return the number of run and failed
        tests."""

        test_spec = self.get_test_json()
        timestamp = datetime.datetime.now().replace(microsecond=0).isoformat()

        xml = ET.Element("testsuites")
        xml.set("name", self.image_name)
        xml.set("timestamp", timestamp)

        result = self.collect_results(
            lambda suite: self.run_suite(suite, xml),
            test_spec["suites"],
            xml)

        # Write XML to file.
        with open(self.artifacts.sponge_xml_path, "wb") as f:
            ET.ElementTree(xml).write(f, encoding='utf-8', xml_declaration=True)

        if result.tests_failed > 0:
            print("[x] FAIL:", result.tests_failed, "of", result.tests_run,
                    "tests failed")
        elif result.tests_run > 0:
            print("    PASS: all", result.tests_run, "tests passed")

        return result


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
    image_name = args.image
    if args.initrd:
        initrd = os.path.join(args.out_initrd, "obj", args.initrd, "initrd.img")
        image_name += "_" + args.initrd
    vm_args = args.vm_args or ""

    # Create class which will manage all test artifacts.
    artifacts = ArtifactsManager(os.path.join(args.log, image_name))

    # Create a driver for the platform we want to test on.
    driver_args = DriverArgs(artifacts, image, initrd, vm_args)
    if args.fvp:
        driver = FvpDriver(driver_args)
    else:
        driver = QemuDriver(driver_args)

    # Create class which will drive test execution.
    runner = TestRunner(artifacts, driver, image_name, args.suite, args.test)

    # Run tests.
    runner_result = runner.run_tests()

    # Print error message if no tests were run as this is probably unexpected.
    # Return suitable error code.
    if runner_result.tests_run == 0:
        print("Error: no tests match")
        return 10
    elif runner_result.tests_failed > 0:
        return 1
    else:
        return 0

if __name__ == "__main__":
    sys.exit(Main())
