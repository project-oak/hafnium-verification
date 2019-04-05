/*
 * Copyright 2019 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdalign.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include "hf/memiter.h"

#include "hftest.h"
#include "hftest_common.h"
#include <sys/reboot.h>

void test_main(int argc, const char *argv[])
{
	const char *command;

	if (argc < 2) {
		HFTEST_LOG("Unable to parse command.");
		return;
	}
	command = argv[1];

	hftest_use_registered_list();

	if (strcmp(command, "json") == 0) {
		hftest_json();
		return;
	}

	if (strcmp(command, "run") == 0) {
		struct memiter suite_name;
		struct memiter test_name;

		if (argc != 4) {
			HFTEST_LOG("Unable to parse test.");
			return;
		}

		memiter_init(&suite_name, argv[2], strnlen_s(argv[2], 64));
		memiter_init(&test_name, argv[3], strnlen_s(argv[3], 64));
		hftest_run(suite_name, test_name);
		return;
	}

	hftest_help();
}

int main(int argc, const char *argv[])
{
	test_main(argc, argv);
	reboot(RB_POWER_OFF);
	return 0;
}
