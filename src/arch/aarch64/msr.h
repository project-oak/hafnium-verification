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

#include <stddef.h>

#define read_msr(name)                                          \
	__extension__({                                         \
		uintreg_t __v;                                  \
		__asm__ volatile("mrs %0, " #name : "=r"(__v)); \
		__v;                                            \
	})

#define write_msr(name, value)                                \
	do {                                                  \
		__asm__ volatile("msr " #name ", %x0"         \
				 :                            \
				 : "rZ"((uintreg_t)(value))); \
	} while (0)
