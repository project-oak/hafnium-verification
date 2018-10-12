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

#ifdef GEN_OFFSETS

/* When generating offsets, create constants which can be extracted from the
 * generated assembly. */

#define DECL(name, type, field) \
	const size_t DEFINE_OFFSET__##name = offsetof(type, field)

#define DECL_SIZE(name, type) const size_t DEFINE_OFFSET__name = sizeof(type)

#else /* GEN_OFFSETS */

/* When not generating offsets, validate that the extracted values are as
 * expected. */

#include <assert.h>

#define DECL(name, type, field) DECL_1(#name, name, offsetof(type, field))
#define DECL_1(name, actual, expected)                       \
	static_assert((actual) == (expected),                \
		      "Offset " name " should be " #expected \
		      " and not " #actual)

#define DECL_SIZE(name, type) DECL_SIZE_1(#name, name, sizeof(type))
#define DECL_SIZE_1(name, actual, expected)                 \
	static_assert((actual) == (expected),               \
		      "Size " #name " should be " #expected \
		      " and not" #actual)

#endif /* GEN_OFFSETS */
