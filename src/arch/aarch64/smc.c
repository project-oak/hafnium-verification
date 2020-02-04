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

#include "smc.h"

#include <stdint.h>

static smc_res_t smc_internal(uint32_t func, uint64_t arg0, uint64_t arg1,
			      uint64_t arg2, uint64_t arg3, uint64_t arg4,
			      uint64_t arg5, uint32_t caller_id)
{
	register uint64_t r0 __asm__("x0") = func;
	register uint64_t r1 __asm__("x1") = arg0;
	register uint64_t r2 __asm__("x2") = arg1;
	register uint64_t r3 __asm__("x3") = arg2;
	register uint64_t r4 __asm__("x4") = arg3;
	register uint64_t r5 __asm__("x5") = arg4;
	register uint64_t r6 __asm__("x6") = arg5;
	register uint64_t r7 __asm__("x7") = caller_id;

	/*
	 * We currently implement SMCCC 1.0, which specifies that the callee can
	 * use x4–x17 as scratch registers. If we move to SMCCC 1.1 then this
	 * will change.
	 */
	__asm__ volatile(
		"smc #0"
		: /* Output registers, also used as inputs ('+' constraint). */
		"+r"(r0), "+r"(r1), "+r"(r2), "+r"(r3), "+r"(r4), "+r"(r5),
		"+r"(r6), "+r"(r7)
		:
		: /* Clobber registers. */
		"x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16",
		"x17");

	return (smc_res_t){.res0 = r0, .res1 = r1, .res2 = r2, .res3 = r3};
}

smc_res_t smc32(uint32_t func, uint32_t arg0, uint32_t arg1, uint32_t arg2,
		uint32_t arg3, uint32_t arg4, uint32_t arg5, uint32_t caller_id)
{
	return smc_internal(func | SMCCC_32_BIT, arg0, arg1, arg2, arg3, arg4,
			    arg5, caller_id);
}

smc_res_t smc64(uint32_t func, uint64_t arg0, uint64_t arg1, uint64_t arg2,
		uint64_t arg3, uint64_t arg4, uint64_t arg5, uint32_t caller_id)
{
	return smc_internal(func | SMCCC_64_BIT, arg0, arg1, arg2, arg3, arg4,
			    arg5, caller_id);
}

smc_res_t smc_forward(uint32_t func, uint64_t arg0, uint64_t arg1,
		      uint64_t arg2, uint64_t arg3, uint64_t arg4,
		      uint64_t arg5, uint32_t caller_id)
{
	return smc_internal(func, arg0, arg1, arg2, arg3, arg4, arg5,
			    caller_id);
}
