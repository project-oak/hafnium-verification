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

#if !defined(__cplusplus)

#include "hf/panic.h"

/**
 * Only use for exceptional cases and never if the condition could be false e.g.
 * when processing external inputs.
 */
#define assert(x)                                                             \
	do {                                                                  \
		if (!(x)) {                                                   \
			panic("assertion failed (%s) at %s:%d", #x, __FILE__, \
			      __LINE__);                                      \
		}                                                             \
	} while (0)

#define static_assert _Static_assert

#endif
