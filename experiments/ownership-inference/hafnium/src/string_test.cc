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

#include <gmock/gmock.h>

extern "C" {
#include "hf/string.h"
}

namespace
{
TEST(string, valid)
{
	struct string str;
	constexpr const char data[] = "test";

	string_init_empty(&str);
	ASSERT_TRUE(string_is_empty(&str));
	ASSERT_STREQ(string_data(&str), "");

	ASSERT_EQ(string_init(&str, data, sizeof(data)), STRING_SUCCESS);
	ASSERT_FALSE(string_is_empty(&str));
	ASSERT_STRNE(string_data(&str), "");
	ASSERT_STREQ(string_data(&str), "test");
}

TEST(string, data_zero_size)
{
	struct string str;
	constexpr const char data[] = "test";

	ASSERT_EQ(string_init(&str, data, 0), STRING_ERROR_INVALID_INPUT);
}

TEST(string, data_no_null_terminator)
{
	struct string str;
	constexpr const char data[] = {'t', 'e', 's', 't'};

	ASSERT_EQ(string_init(&str, data, sizeof(data)),
		  STRING_ERROR_INVALID_INPUT);
}

TEST(string, data_two_null_terminators)
{
	struct string str;
	constexpr const char data[] = {'\0', 't', 'e', 's', 't', '\0'};

	ASSERT_EQ(string_init(&str, data, sizeof(data)),
		  STRING_ERROR_INVALID_INPUT);
}

} /* namespace */
