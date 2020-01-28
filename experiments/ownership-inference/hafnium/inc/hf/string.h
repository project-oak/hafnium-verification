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

#pragma once

#include <stdbool.h>
#include <stddef.h>

/**
 * Maximum length of a string including the NULL terminator.
 * This is an arbitrary number and can be adjusted to fit use cases.
 */
#define STRING_MAX_SIZE 32

enum string_return_code {
	STRING_SUCCESS,
	STRING_ERROR_INVALID_INPUT,
	STRING_ERROR_TOO_LONG,
};

/**
 * Statically-allocated string data structure with input validation to ensure
 * strings are properly NULL-terminated.
 *
 * This is intentionally kept as simple as possible and should not be extended
 * to perform complex string operations without a good use case.
 */
struct string {
	char data[STRING_MAX_SIZE];
};

/**
 * Macro to initialize `struct string` from a string constant.
 * Triggers a compilation error if the string does not fit into the buffer.
 */
#define STRING_INIT(str) ((struct string){.data = str})

enum string_return_code string_init(struct string *str, const char *data,
				    size_t size);
void string_init_empty(struct string *str);
bool string_is_empty(const struct string *str);
const char *string_data(const struct string *str);
