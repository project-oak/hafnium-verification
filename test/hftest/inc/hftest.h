/*
 * Copyright 2018 Google LLC
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

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "hf/dlog.h"

/*
 * Define a set up function to be run before every test in a test suite.
 */
#define SET_UP(suite) HFTEST_SET_UP(suite)

/*
 * Define a tear down function to be run after every test in a test suite.
 */
#define TEAR_DOWN(suite) HFTEST_TEAR_DOWN(suite)

/*
 * Define a test as part of a test suite.
 */
#define TEST(suite, test) HFTEST_TEST(suite, test)

/* Assertions. */
#define ASSERT_EQ(x, y) ASSERT_OP(x, y, ==, true)
#define ASSERT_NE(x, y) ASSERT_OP(x, y, !=, true)
#define ASSERT_LE(x, y) ASSERT_OP(x, y, <=, true)
#define ASSERT_LT(x, y) ASSERT_OP(x, y, <, true)
#define ASSERT_GE(x, y) ASSERT_OP(x, y, >=, true)
#define ASSERT_GT(x, y) ASSERT_OP(x, y, >, true)

#define ASSERT_TRUE(x) ASSERT_EQ(x, true);
#define ASSERT_FALSE(x) ASSERT_EQ(x, false);

#define EXPECT_EQ(x, y) ASSERT_OP(x, y, ==, false)
#define EXPECT_NE(x, y) ASSERT_OP(x, y, !=, false)
#define EXPECT_LE(x, y) ASSERT_OP(x, y, <=, false)
#define EXPECT_LT(x, y) ASSERT_OP(x, y, <, false)
#define EXPECT_GE(x, y) ASSERT_OP(x, y, >=, false)
#define EXPECT_GT(x, y) ASSERT_OP(x, y, >, false)

#define EXPECT_TRUE(x) EXPECT_EQ(x, true);
#define EXPECT_FALSE(x) EXPECT_EQ(x, false);

/*
 * This must be used exactly once in a test image to signal to the linker that
 * the .hftest section is allowed to be included in the generated image.
 */
#define HFTEST_ENABLE() int hftest_enable

/*
 * Prefixed to log lines from tests for easy filtering in the console.
 */
#define HFTEST_LOG_PREFIX "[hftest] "

/* Above this point is the public API. Below are the implementation details. */

/* Log with the HFTEST_LOG_PREFIX and a new line. The zero is added so there is
 * always at least one variadic argument. */
#define HFTEST_LOG(...) HFTEST_LOG_IMPL(__VA_ARGS__, 0)
#define HFTEST_LOG_IMPL(format, ...) \
	dlog("%s" format "\n", HFTEST_LOG_PREFIX, __VA_ARGS__)

/* Helper to wrap the argument in quotes. */
#define HFTEST_STR(str) #str

/* Sections are names such that when the linker sorts them, all entries for the
 * same test suite are contiguous and the set up and tear down entries come
 * before the tests. This order simplifies test discovery in the running image.
 */
#define HFTEST_SET_UP_SECTION(suite_name) \
	HFTEST_STR(.hftest.suite_name .1set_up)
#define HFTEST_TEAR_DOWN_SECTION(suite_name) \
	HFTEST_STR(.hftest.suite_name .1tear_down)
#define HFTEST_TEST_SECTION(suite_name, test_name) \
	HFTEST_STR(.hftest.suite_name .2test.test_name)

/* Helpers to construct unique identifiers. */
#define HFTEST_SET_UP_STRUCT(suite_name) hftest_set_up_##suite_name
#define HFTEST_TEAR_DOWN_STRUCT(suite_name) hftest_tear_down_##suite_name
#define HFTEST_TEST_STRUCT(suite_name, test_name) \
	hftest_test_##suite_name##_##test_name

#define HFTEST_SET_UP_FN(suite_name) hftest_set_up_fn_##suite_name
#define HFTEST_TEAR_DOWN_FN(suite_name) hftest_tear_down_fn_##suite_name
#define HFTEST_TEST_FN(suite_name, test_name) \
	hftest_test_fn_##suite_name##_##test_name

/* Register test functions. */
#define HFTEST_SET_UP(suite_name)                                           \
	static void HFTEST_SET_UP_FN(suite_name)(struct hftest_context *    \
						 hftest_ctx);               \
	const struct hftest_test __attribute__((used))                      \
		__attribute__((section(HFTEST_SET_UP_SECTION(suite_name)))) \
			HFTEST_SET_UP_STRUCT(suite_name) = {                \
				.suite = #suite_name,                       \
				.kind = HFTEST_KIND_SET_UP,                 \
				.fn = HFTEST_SET_UP_FN(suite_name),         \
	};                                                                  \
	static void HFTEST_SET_UP_FN(suite_name)(                           \
		__attribute__((unused)) struct hftest_context * hftest_ctx)

#define HFTEST_TEAR_DOWN(suite_name)                                           \
	static void HFTEST_TEAR_DOWN_FN(suite_name)(struct hftest_context *    \
						    hftest_ctx);               \
	const struct hftest_test __attribute__((used))                         \
		__attribute__((section(HFTEST_TEAR_DOWN_SECTION(suite_name)))) \
			HFTEST_TEAR_DOWN_STRUCT(suite_name) = {                \
				.suite = #suite_name,                          \
				.kind = HFTEST_KIND_TEAR_DOWN,                 \
				.fn = HFTEST_TEAR_DOWN_FN(suite_name),         \
	};                                                                     \
	static void HFTEST_TEAR_DOWN_FN(suite_name)(                           \
		__attribute__((unused)) struct hftest_context * hftest_ctx)

#define HFTEST_TEST(suite_name, test_name)                                  \
	static void HFTEST_TEST_FN(                                         \
		suite_name, test_name)(struct hftest_context * hftest_ctx); \
	const struct hftest_test __attribute__((used)) __attribute__(       \
		(section(HFTEST_TEST_SECTION(suite_name, test_name))))      \
		HFTEST_TEST_STRUCT(suite_name, test_name) = {               \
			.suite = #suite_name,                               \
			.kind = HFTEST_KIND_TEST,                           \
			.name = #test_name,                                 \
			.fn = HFTEST_TEST_FN(suite_name, test_name),        \
	};                                                                  \
	static void HFTEST_TEST_FN(suite_name, test_name)(                  \
		__attribute__((unused)) struct hftest_context * hftest_ctx)

/* Context for tests. */
struct hftest_context {
	uint32_t failures;
};

/* A test case. */
typedef void (*hftest_test_fn)(struct hftest_context *);

enum hftest_kind {
	HFTEST_KIND_SET_UP = 0,
	HFTEST_KIND_TEST = 1,
	HFTEST_KIND_TEAR_DOWN = 2,
};

struct hftest_test {
	const char *suite;
	enum hftest_kind kind;
	const char *name;
	hftest_test_fn fn;
};

/*
 * This union can store any of the primitive types supported by the assertion
 * macros.
 *
 * It does not include pointers as comparison of pointers is not often needed
 * and could be a mistake for string comparison. If pointer comparison is needed
 * and explicit assertion such as ASSERT_PTR_EQ() would be more appropriate.
 */
union hftest_any {
	bool b;
	char c;
	signed char sc;
	unsigned char uc;
	signed short ss;
	unsigned short us;
	signed int si;
	unsigned int ui;
	signed long int sli;
	unsigned long int uli;
	signed long long int slli;
	unsigned long long int ulli;
};

/* _Generic formatting doesn't seem to be supported so doing this manually. */
/* clang-format off */

/* Select the union member to match the type of the expression. */
#define hftest_any_get(any, x)                      \
	_Generic((x),                               \
		bool:                   (any).b,    \
		char:                   (any).c,    \
		signed char:            (any).sc,   \
		unsigned char:          (any).uc,   \
		signed short:           (any).ss,   \
		unsigned short:         (any).us,   \
		signed int:             (any).si,   \
		unsigned int:           (any).ui,   \
		signed long int:        (any).sli,  \
		unsigned long int:      (any).uli,  \
		signed long long int:   (any).slli, \
		unsigned long long int: (any).ulli)

/*
 * dlog format specifier for types. Note, these aren't the standard specifiers
 * for the types.
 */
#define hftest_dlog_format(x)                 \
	_Generic((x),                         \
		bool:                   "%u", \
		char:                   "%c", \
		signed char:            "%d", \
		unsigned char:          "%u", \
		signed short:           "%d", \
		unsigned short:         "%u", \
		signed int:             "%d", \
		unsigned int:           "%u", \
		signed long int:        "%d", \
		unsigned long int:      "%u", \
		signed long long int:   "%d", \
		unsigned long long int: "%u")

/* clang-format on */

#define ASSERT_OP(lhs, rhs, op, fatal)                                         \
	do {                                                                   \
		union hftest_any lhs_value;                                    \
		union hftest_any rhs_value;                                    \
		hftest_any_get(lhs_value, lhs) = (lhs);                        \
		hftest_any_get(rhs_value, rhs) = (rhs);                        \
		if (!(hftest_any_get(lhs_value, lhs)                           \
			      op hftest_any_get(rhs_value, rhs))) {            \
			++hftest_ctx->failures;                                \
			dlog(HFTEST_LOG_PREFIX "  %s:%u: Failure\n", __FILE__, \
			     __LINE__);                                        \
			dlog(HFTEST_LOG_PREFIX "    %s %s %s (%s=", #lhs, #op, \
			     #rhs, #lhs);                                      \
			dlog(hftest_dlog_format(lhs),                          \
			     hftest_any_get(lhs_value, lhs));                  \
			dlog(", %s=", #rhs);                                   \
			dlog(hftest_dlog_format(rhs),                          \
			     hftest_any_get(rhs_value, rhs));                  \
			dlog(")\n");                                           \
			if (fatal) {                                           \
				return;                                        \
			}                                                      \
		}                                                              \
	} while (0)
