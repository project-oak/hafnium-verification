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

#include "hf/dlog.h"

#include "hftest.h"

/**
 * Test that logs are written to the buffer, and the rest is empty.
 */
TEST(dlog, log_buffer)
{
	const char test_string[] = "Test string\n";

	dlog(test_string);
	ASSERT_EQ(strcmp(test_string, dlog_buffer), 0);
	/* The \0 at the end shouldn't be counted. */
	ASSERT_EQ(dlog_buffer_offset, sizeof(test_string) - 1);
	for (int i = sizeof(test_string) - 1; i < DLOG_BUFFER_SIZE; ++i) {
		EXPECT_EQ(dlog_buffer[i], '\0');
	}
}
