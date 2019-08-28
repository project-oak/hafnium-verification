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

#include "hf/arch/std.h"

typedef size_t rsize_t;

/**
 * Restrict the maximum range for range checked functions so as to be more
 * likely to catch errors. This may need to be relaxed if it proves to be overly
 * restrictive.
 */
#define RSIZE_MAX (128 * 1024 * 1024)

/*
 * Only the safer versions of these functions are exposed to reduce the chance
 * of misusing the versions without bounds checking or null pointer checks.
 *
 * These functions don't return errno_t as per the specification and implicitly
 * have a constraint handler that panics.
 */
void memset_s(void *dest, rsize_t destsz, int ch, rsize_t count);
void memcpy_s(void *dest, rsize_t destsz, const void *src, rsize_t count);
void memmove_s(void *dest, rsize_t destsz, const void *src, rsize_t count);

void *memchr(const void *ptr, int ch, size_t count);

size_t strnlen_s(const char *str, size_t strsz);
