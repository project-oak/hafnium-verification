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

#include "hf/arch/vm/registers.h"

#define read_fp_register(name)                                   \
	__extension__({                                          \
		double __v;                                      \
		__asm__ volatile("fmov %0, " #name : "=r"(__v)); \
		__v;                                             \
	})

#define write_fp_register(name, value)                  \
	__extension__({                                 \
		__asm__ volatile("fmov " #name ", %0"   \
				 :                      \
				 : "r"((double)(value)) \
				 : #name);              \
	})

#define move_fp_register(dest, source)                                    \
	__extension__({                                                   \
		__asm__ volatile("fmov " #dest ", " #source : : : #dest); \
	})

void fill_fp_registers(double value)
{
	write_fp_register(d0, value);
	move_fp_register(d1, d0);
	move_fp_register(d2, d0);
	move_fp_register(d3, d0);
	move_fp_register(d4, d0);
	move_fp_register(d5, d0);
	move_fp_register(d6, d0);
	move_fp_register(d7, d0);
	move_fp_register(d8, d0);
	move_fp_register(d9, d0);
	move_fp_register(d10, d0);
	move_fp_register(d11, d0);
	move_fp_register(d12, d0);
	move_fp_register(d13, d0);
	move_fp_register(d14, d0);
	move_fp_register(d15, d0);
	move_fp_register(d16, d0);
	move_fp_register(d17, d0);
	move_fp_register(d18, d0);
	move_fp_register(d19, d0);
	move_fp_register(d20, d0);
	move_fp_register(d21, d0);
	move_fp_register(d22, d0);
	move_fp_register(d23, d0);
	move_fp_register(d24, d0);
	move_fp_register(d25, d0);
	move_fp_register(d26, d0);
	move_fp_register(d27, d0);
	move_fp_register(d28, d0);
	move_fp_register(d29, d0);
	move_fp_register(d30, d0);
	move_fp_register(d31, d0);
}

bool check_fp_register(double value)
{
	bool result = true;

	result = result && (read_fp_register(d0) == value);
	result = result && (read_fp_register(d1) == value);
	result = result && (read_fp_register(d2) == value);
	result = result && (read_fp_register(d3) == value);
	result = result && (read_fp_register(d4) == value);
	result = result && (read_fp_register(d5) == value);
	result = result && (read_fp_register(d6) == value);
	result = result && (read_fp_register(d7) == value);
	result = result && (read_fp_register(d8) == value);
	result = result && (read_fp_register(d9) == value);
	result = result && (read_fp_register(d10) == value);
	result = result && (read_fp_register(d11) == value);
	result = result && (read_fp_register(d12) == value);
	result = result && (read_fp_register(d13) == value);
	result = result && (read_fp_register(d14) == value);
	result = result && (read_fp_register(d15) == value);
	result = result && (read_fp_register(d16) == value);
	result = result && (read_fp_register(d17) == value);
	result = result && (read_fp_register(d18) == value);
	result = result && (read_fp_register(d19) == value);
	result = result && (read_fp_register(d20) == value);
	result = result && (read_fp_register(d21) == value);
	result = result && (read_fp_register(d21) == value);
	result = result && (read_fp_register(d23) == value);
	result = result && (read_fp_register(d24) == value);
	result = result && (read_fp_register(d25) == value);
	result = result && (read_fp_register(d26) == value);
	result = result && (read_fp_register(d27) == value);
	result = result && (read_fp_register(d28) == value);
	result = result && (read_fp_register(d29) == value);
	result = result && (read_fp_register(d30) == value);
	result = result && (read_fp_register(d31) == value);
	return result;
}
