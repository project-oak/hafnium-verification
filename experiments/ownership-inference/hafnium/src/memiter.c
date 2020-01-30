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

#include "hf/memiter.h"

#include "hf/dlog.h"
#include "hf/std.h"

/**
 * Initialises the given memory iterator.
 */
void memiter_init(struct memiter *it, const void *data, size_t size)
{
	it->next = data;
	it->limit = it->next + size;
}

/**
 * Determines if the next character is a whitespace.
 */
static bool memiter_isspace(struct memiter *it)
{
	switch (*it->next) {
	case ' ':
	case '\t':
	case '\n':
	case '\r':
		return true;
	default:
		return false;
	}
}

/**
 * Moves iterator to the next non-whitespace character.
 */
static void memiter_skip_space(struct memiter *it)
{
	while (it->next < it->limit && memiter_isspace(it)) {
		it->next++;
	}
}

/**
 * Compares the iterator to a null-terminated string.
 */
bool memiter_iseq(const struct memiter *it, const char *str)
{
	size_t it_len = it->limit - it->next;
	size_t len = strnlen_s(str, it_len + 1);

	if (len != it_len) {
		return false;
	}

	return memcmp(it->next, str, len) == 0;
}

/**
 * Retrieves the next string that is delimited by whitespaces. The result is
 * stored in "str".
 */
bool memiter_parse_str(struct memiter *it, struct memiter *str)
{
	/* Skip all white space and fail if we reach the end of the buffer. */
	memiter_skip_space(it);
	if (it->next >= it->limit) {
		return false;
	}

	str->next = it->next;

	/* Find the end of the string. */
	while (it->next < it->limit && !memiter_isspace(it)) {
		it->next++;
	}

	str->limit = it->next;

	return true;
}

/**
 * Parses the next string that represents a 64-bit number.
 */
bool memiter_parse_uint(struct memiter *it, uint64_t *value)
{
	uint64_t v = 0;

	/* Skip all white space and fail if we reach the end of the buffer. */
	memiter_skip_space(it);
	if (it->next >= it->limit) {
		return false;
	}

	/* Fail if it's not a number. */
	if (*it->next < '0' || *it->next > '9') {
		return false;
	}

	/* Parse the number. */
	do {
		v = v * 10 + *it->next - '0';
		it->next++;
	} while (it->next < it->limit && *it->next >= '0' && *it->next <= '9');

	*value = v;

	return true;
}

/**
 * Advances the iterator by the given number of bytes. Returns true if the
 * iterator was advanced without going over its limit; returns false and leaves
 * the iterator unmodified otherwise.
 */
bool memiter_advance(struct memiter *it, size_t v)
{
	const char *p = it->next + v;

	if (p < it->next || p > it->limit) {
		return false;
	}

	it->next = p;

	return true;
}

const void *memiter_base(const struct memiter *it)
{
	return (const void *)it->next;
}

/**
 * Returns the number of bytes in interval [it.next, it.limit).
 */
size_t memiter_size(const struct memiter *it)
{
	return it->limit - it->next;
}
