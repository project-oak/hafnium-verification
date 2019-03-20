/*
 * Copyright 2018 The Hafnium Authors.
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

#include "hftest_common.h"

#include "hf/arch/vm/power_mgmt.h"

#include "hf/boot_params.h"
#include "hf/fdt_handler.h"
#include "hf/memiter.h"
#include "hf/std.h"

#include "hftest.h"

HFTEST_ENABLE();

static struct hftest_test hftest_constructed[HFTEST_MAX_TESTS];
static size_t hftest_count;
static struct hftest_test *hftest_list;

static struct hftest_context global_context;

struct hftest_context *hftest_get_context(void)
{
	return &global_context;
}

/**
 * Adds the given test information to the global list, to be used by
 * `hftest_use_registered_list`.
 */
void hftest_register(struct hftest_test test)
{
	if (hftest_count < HFTEST_MAX_TESTS) {
		hftest_constructed[hftest_count++] = test;
	} else {
		HFTEST_FAIL(true, "Too many tests");
	}
}

/**
 * Uses the list of tests registered by `hftest_register(...)` as the ones to
 * run.
 */
void hftest_use_registered_list(void)
{
	hftest_list = hftest_constructed;
}

/**
 * Uses the given list of tests as the ones to run.
 */
void hftest_use_list(struct hftest_test list[], size_t count)
{
	hftest_list = list;
	hftest_count = count;
}

/**
 * Writes out a JSON structure describing the available tests.
 */
void hftest_json(void)
{
	const char *suite = NULL;
	size_t i;
	size_t suites_in_image = 0;
	size_t tests_in_suite = 0;

	HFTEST_LOG("{");
	HFTEST_LOG("  \"suites\": [");
	for (i = 0; i < hftest_count; ++i) {
		struct hftest_test *test = &hftest_list[i];
		if (test->suite != suite) {
			/* Close out previously open suite. */
			if (tests_in_suite) {
				HFTEST_LOG("      ]");
				HFTEST_LOG("    },");
			}
			/* Move onto new suite. */
			++suites_in_image;
			suite = test->suite;
			tests_in_suite = 0;
			HFTEST_LOG("    {");
			HFTEST_LOG("      \"name\": \"%s\",", test->suite);
		}
		if (test->kind == HFTEST_KIND_SET_UP) {
			HFTEST_LOG("      \"setup\": true,");
		}
		if (test->kind == HFTEST_KIND_TEAR_DOWN) {
			HFTEST_LOG("      \"teardown\": true,");
		}
		if (test->kind == HFTEST_KIND_TEST) {
			if (!tests_in_suite) {
				HFTEST_LOG("      \"tests\": [");
			}
			/*
			 * It's easier to put the comma at the start of the line
			 * than the end even though the JSON looks a bit funky.
			 */
			HFTEST_LOG("       %c\"%s\"",
				   tests_in_suite ? ',' : ' ', test->name);
			++tests_in_suite;
		}
	}
	if (tests_in_suite) {
		HFTEST_LOG("      ]");
		HFTEST_LOG("    }");
	}
	HFTEST_LOG("  ]");
	HFTEST_LOG("}");
}

/**
 * Logs a failure message and shut down.
 */
noreturn void abort(void)
{
	HFTEST_LOG("FAIL");
	arch_power_off();
}

static void run_test(hftest_test_fn set_up, hftest_test_fn test,
		     hftest_test_fn tear_down, const struct fdt_header *fdt)
{
	/* Prepare the context. */
	struct hftest_context *ctx = hftest_get_context();
	memset_s(ctx, sizeof(*ctx), 0, sizeof(*ctx));
	ctx->abort = abort;
	ctx->fdt = fdt;

	/* Run any set up functions. */
	if (set_up) {
		set_up();
		if (ctx->failures) {
			abort();
		}
	}

	/* Run the test. */
	test();
	if (ctx->failures) {
		abort();
	}

	/* Run any tear down functions. */
	if (tear_down) {
		tear_down();
		if (ctx->failures) {
			abort();
		}
	}

	HFTEST_LOG("FINISHED");
}

/**
 * Runs the given test case.
 */
void hftest_run(struct memiter suite_name, struct memiter test_name,
		const struct fdt_header *fdt)
{
	size_t i;
	bool found_suite = false;
	const char *suite = NULL;
	hftest_test_fn suite_set_up = NULL;
	hftest_test_fn suite_tear_down = NULL;

	for (i = 0; i < hftest_count; ++i) {
		struct hftest_test *test = &hftest_list[i];
		/* Find the test suite. */
		if (found_suite) {
			if (test->suite != suite) {
				/* Test wasn't in the suite. */
				break;
			}
		} else {
			if (test->suite == suite) {
				/* This isn't the right suite so keep going. */
				continue;
			}
			/* Examine a new suite. */
			suite = test->suite;
			if (memiter_iseq(&suite_name, test->suite)) {
				found_suite = true;
			}
		}

		switch (test->kind) {
		/*
		 * The first entries in the suite are the set up and tear down
		 * functions.
		 */
		case HFTEST_KIND_SET_UP:
			suite_set_up = test->fn;
			break;
		case HFTEST_KIND_TEAR_DOWN:
			suite_tear_down = test->fn;
			break;
		/* Find the test. */
		case HFTEST_KIND_TEST:
			if (memiter_iseq(&test_name, test->name)) {
				run_test(suite_set_up, test->fn,
					 suite_tear_down, fdt);
				return;
			}
			break;
		default:
			/* Ignore other kinds. */
			break;
		}
	}

	HFTEST_LOG("Unable to find requested tests.");
}

/**
 * Writes out usage information.
 */
void hftest_help(void)
{
	HFTEST_LOG("usage:");
	HFTEST_LOG("");
	HFTEST_LOG("  help");
	HFTEST_LOG("");
	HFTEST_LOG("    Show this help.");
	HFTEST_LOG("");
	HFTEST_LOG("  json");
	HFTEST_LOG("");
	HFTEST_LOG(
		"    Print a directory of test suites and tests in "
		"JSON "
		"format.");
	HFTEST_LOG("");
	HFTEST_LOG("  run <suite> <test>");
	HFTEST_LOG("");
	HFTEST_LOG("    Run the named test from the named test suite.");
}

static uintptr_t vcpu_index_to_id(size_t index)
{
	/* For now we use indices as IDs for vCPUs. */
	return index;
}

/**
 * Get the ID of the CPU with the given index.
 */
uintptr_t hftest_get_cpu_id(size_t index)
{
	struct boot_params params;
	struct fdt_node n;
	const struct fdt_header *fdt = hftest_get_context()->fdt;

	if (fdt == NULL) {
		/*
		 * We must be in a service VM, so apply the mapping that Hafnium
		 * uses for vCPU IDs.
		 */
		return vcpu_index_to_id(index);
	}

	/* Find physical CPU ID from FDT. */
	if (!fdt_root_node(&n, fdt)) {
		FAIL("FDT failed validation.");
	}
	if (!fdt_find_child(&n, "")) {
		FAIL("Unable to find FDT root node.");
	}
	fdt_find_cpus(&n, params.cpu_ids, &params.cpu_count);

	return params.cpu_ids[index];
}
