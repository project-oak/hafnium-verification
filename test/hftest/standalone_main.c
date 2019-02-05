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

#include "hf/fdt.h"
#include "hf/memiter.h"

#include "hftest.h"
#include "hftest_common.h"

alignas(4096) uint8_t kstack[4096];

extern struct hftest_test hftest_begin[];
extern struct hftest_test hftest_end[];

void kmain(const struct fdt_header *fdt)
{
	struct fdt_node n;
	const char *bootargs;
	uint32_t bootargs_size;
	struct memiter bootargs_iter;
	struct memiter command;

	hftest_use_list(hftest_begin, hftest_end - hftest_begin);

	if (!fdt_root_node(&n, fdt)) {
		HFTEST_LOG("FDT failed validation.");
		return;
	}

	if (!fdt_find_child(&n, "")) {
		HFTEST_LOG("Unable to find root node in FDT.");
		return;
	}

	if (!fdt_find_child(&n, "chosen")) {
		HFTEST_LOG("Unable to find 'chosen' node in FDT.");
		return;
	}

	if (!fdt_read_property(&n, "bootargs", &bootargs, &bootargs_size)) {
		HFTEST_LOG("Unable to read bootargs.");
		return;
	}

	/* Remove null terminator. */
	memiter_init(&bootargs_iter, bootargs, bootargs_size - 1);

	if (!memiter_parse_str(&bootargs_iter, &command)) {
		HFTEST_LOG("Unable to parse command.");
		return;
	}

	if (memiter_iseq(&command, "json")) {
		hftest_json();
		return;
	}

	if (memiter_iseq(&command, "run")) {
		struct memiter suite_name;
		struct memiter test_name;

		if (!memiter_parse_str(&bootargs_iter, &suite_name)) {
			HFTEST_LOG("Unable to parse test suite.");
			return;
		}

		if (!memiter_parse_str(&bootargs_iter, &test_name)) {
			HFTEST_LOG("Unable to parse test.");
			return;
		}
		hftest_run(suite_name, test_name);
		return;
	}

	hftest_help();
}
