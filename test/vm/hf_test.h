#ifndef _HF_TEST_H
#define _HF_TEST_H

#include <stdbool.h>
#include <stdint.h>

#include "dlog.h"

/*
 * Prefixed to log lines from tests for easy filtering in the console.
 */
#define HF_TEST_LOG_PREFIX "[hf_test] "

/*
 * Context for tests.
 */
struct hf_test_context {
	uint32_t failures;
};

/*
 * This union can store any of the primitive types supported by the assertion
 * macros.
 */
union hf_test_any {
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
	void *p;
};

/* _Generic formatting doesn't seem to be supported so doing this manually. */
/* clang-format off */

/* Select the union member to match the type of the expression. */
#define hf_test_any_get(any, x)                     \
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
		unsigned long long int: (any).ulli, \
		void *:                 (any).p)

/*
 * dlog format specifier for types. Note, these aren't the standard specifiers
 * for the types.
 */
#define hf_test_dlog_format(x)                \
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
		unsigned long long int: "%u", \
		void *:                 "%p")

/* clang-format on */

#define ASSERT_OP(lhs, rhs, op, fatal)                                     \
	do {                                                               \
		union hf_test_any lhs_value;                               \
		union hf_test_any rhs_value;                               \
		hf_test_any_get(lhs_value, lhs) = (lhs);                   \
		hf_test_any_get(rhs_value, rhs) = (rhs);                   \
		if (!(hf_test_any_get(lhs_value, lhs)                      \
			      op hf_test_any_get(rhs_value, rhs))) {       \
			++hf_test_ctx->failures;                           \
			dlog(HF_TEST_LOG_PREFIX "  %s:%u: Failure\n",      \
			     __FILE__, __LINE__);                          \
			dlog(HF_TEST_LOG_PREFIX "    %s %s %s (%s=", #lhs, \
			     #op, #rhs, #lhs);                             \
			dlog(hf_test_dlog_format(lhs),                     \
			     hf_test_any_get(lhs_value, lhs));             \
			dlog(", %s=", #rhs);                               \
			dlog(hf_test_dlog_format(rhs),                     \
			     hf_test_any_get(rhs_value, rhs));             \
			dlog(")\n");                                       \
			if (fatal) {                                       \
				return;                                    \
			}                                                  \
		}                                                          \
	} while (0)

#define ASSERT_EQ(x, y) ASSERT_OP(x, y, ==, true)
#define ASSERT_NE(x, y) ASSERT_OP(x, y, !=, true)
#define ASSERT_LE(x, y) ASSERT_OP(x, y, <=, true)
#define ASSERT_LT(x, y) ASSERT_OP(x, y, <, true)
#define ASSERT_GE(x, y) ASSERT_OP(x, y, >=, true)
#define ASSERT_GT(x, y) ASSERT_OP(x, y, >, true)

#define EXPECT_EQ(x, y) ASSERT_OP(x, y, ==, false)
#define EXPECT_NE(x, y) ASSERT_OP(x, y, !=, false)
#define EXPECT_LE(x, y) ASSERT_OP(x, y, <=, false)
#define EXPECT_LT(x, y) ASSERT_OP(x, y, <, false)
#define EXPECT_GE(x, y) ASSERT_OP(x, y, >=, false)
#define EXPECT_GT(x, y) ASSERT_OP(x, y, >, false)

/*
 * Declare a test case.
 */
#define TEST(name) static void name(struct hf_test_context *hf_test_ctx)

/*
 * Run a test case.
 */
#define RUN_TEST(test)                                       \
	do {                                                 \
		struct hf_test_context ctx = {               \
			.failures = 0,                       \
		};                                           \
		dlog(HF_TEST_LOG_PREFIX "RUN %s\n", #test);  \
		test(&ctx);                                  \
		if (ctx.failures) {                          \
			dlog(HF_TEST_LOG_PREFIX "FAILED\n"); \
		} else {                                     \
			dlog(HF_TEST_LOG_PREFIX "OK\n");     \
		}                                            \
	} while (0)

#endif /* _HF_TEST_H */
