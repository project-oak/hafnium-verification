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

/*
 * Define a test service.
 */
#define TEST_SERVICE(service) HFTEST_TEST_SERVICE(service)

/* Assertions. */
#define ASSERT_EQ(x, y) HFTEST_ASSERT_OP(x, y, ==, true)
#define ASSERT_NE(x, y) HFTEST_ASSERT_OP(x, y, !=, true)
#define ASSERT_LE(x, y) HFTEST_ASSERT_OP(x, y, <=, true)
#define ASSERT_LT(x, y) HFTEST_ASSERT_OP(x, y, <, true)
#define ASSERT_GE(x, y) HFTEST_ASSERT_OP(x, y, >=, true)
#define ASSERT_GT(x, y) HFTEST_ASSERT_OP(x, y, >, true)

#define ASSERT_TRUE(x) ASSERT_EQ(x, true)
#define ASSERT_FALSE(x) ASSERT_EQ(x, false)

#define EXPECT_EQ(x, y) HFTEST_ASSERT_OP(x, y, ==, false)
#define EXPECT_NE(x, y) HFTEST_ASSERT_OP(x, y, !=, false)
#define EXPECT_LE(x, y) HFTEST_ASSERT_OP(x, y, <=, false)
#define EXPECT_LT(x, y) HFTEST_ASSERT_OP(x, y, <, false)
#define EXPECT_GE(x, y) HFTEST_ASSERT_OP(x, y, >=, false)
#define EXPECT_GT(x, y) HFTEST_ASSERT_OP(x, y, >, false)

#define EXPECT_TRUE(x) EXPECT_EQ(x, true)
#define EXPECT_FALSE(x) EXPECT_EQ(x, false)

#define FAIL(...) HFTEST_FAIL(true, __VA_ARGS__)

/* Service utilities. */
#define SERVICE_NAME_MAX_LENGTH 64
#define SERVICE_SELECT(vm_id, service, send_buffer) \
	HFTEST_SERVICE_SELECT(vm_id, service, send_buffer)

#define SERVICE_SEND_BUFFER() HFTEST_SERVICE_SEND_BUFFER()
#define SERVICE_RECV_BUFFER() HFTEST_SERVICE_RECV_BUFFER()
#define SERVICE_MEMORY_SIZE() HFTEST_SERVICE_MEMORY_SIZE()

/*
 * This must be used exactly once in a test image to signal to the linker that
 * the .hftest section is allowed to be included in the generated image.
 */
#define HFTEST_ENABLE() int hftest_enable

/*
 * Prefixed to log lines from tests for easy filtering in the console.
 */
#define HFTEST_LOG_PREFIX "[hftest] "

/*
 * Indentation used e.g. to give the reason for an assertion failure.
 */
#define HFTEST_LOG_INDENT "    "

uintptr_t hftest_get_cpu_id(size_t index);

/* Above this point is the public API. Now include the implementation. */
#include <hftest_impl.h>
