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

#include "hf/panic.h"

/**
 * Only use to check assumptions which, if false, mean the system is in a bad
 * state and it is unsafe to continue.
 *
 * Do not use if the condition could ever be legitimately false e.g. when
 * processing external inputs.
 */
#define CHECK(x)                                                              \
	do {                                                                  \
		if (!(x)) {                                                   \
			panic("assertion failed (%s) at %s:%d", #x, __FILE__, \
			      __LINE__);                                      \
		}                                                             \
	} while (0)
