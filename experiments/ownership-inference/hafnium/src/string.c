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

#include "hf/string.h"

#include "hf/static_assert.h"
#include "hf/std.h"

void string_init_empty(struct string *str)
{
	static_assert(sizeof(str->data) >= 1, "String buffer too small");
	str->data[0] = '\0';
}

/**
 * Caller must guarantee that `data` points to a NULL-terminated string.
 * The constructor checks that it fits into the internal buffer and copies
 * the string there.
 */
enum string_return_code string_init(struct string *str, const char *data,
				    size_t size)
{
	/*
	 * Require that the value contains exactly one NULL character and that
	 * it is the last byte.
	 */
	if (size < 1 || memchr(data, '\0', size) != &data[size - 1]) {
		return STRING_ERROR_INVALID_INPUT;
	}

	if (size > sizeof(str->data)) {
		return STRING_ERROR_TOO_LONG;
	}

	memcpy_s(str->data, sizeof(str->data), data, size);
	return STRING_SUCCESS;
}

bool string_is_empty(const struct string *str)
{
	return str->data[0] == '\0';
}

const char *string_data(const struct string *str)
{
	return str->data;
}
