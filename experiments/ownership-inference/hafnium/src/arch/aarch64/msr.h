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

#pragma once

#include <stddef.h>

#include "hf/arch/cpu.h"

/**
 * Macros to stringify a parameter, and to allow the results of a macro to be
 * stringified in turn.
 */
#define str_(s) #s
#define str(s) str_(s)

/**
 * Reads a system register, supported by the current assembler, and returns the
 * result.
 */
#define read_msr(name)                                              \
	__extension__({                                             \
		uintreg_t __v;                                      \
		__asm__ volatile("mrs %0, " str(name) : "=r"(__v)); \
		__v;                                                \
	})

/**
 * Writes the value to the system register, supported by the current assembler.
 */
#define write_msr(name, value)                                \
	__extension__({                                       \
		__asm__ volatile("msr " str(name) ", %x0"     \
				 :                            \
				 : "rZ"((uintreg_t)(value))); \
	})

/*
 * Encodings for registers supported after Armv8.0.
 * We aim to build one binary that supports a variety of platforms, therefore,
 * use encodings in Arm Architecture Reference Manual Armv8-a, D13.2 for
 * registers supported after Armv8.0.
 */

/*
 * Registers supported from Armv8.1 onwards.
 */

/*
 * Registers for feature Armv8.1-LOR (Limited Ordering Regions).
 */

/**
 * Encoding for the LORegion Control register (LORC_EL1).
 * This register enables and disables LORegions (Armv8.1).
 */
#define MSR_LORC_EL1 S3_0_C10_C4_3
