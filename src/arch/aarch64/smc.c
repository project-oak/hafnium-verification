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

smc_res_t smc_internal(uint32_t func, uint64_t arg0, uint64_t arg1,
		       uint64_t arg2, uint64_t arg3, uint64_t arg4,
		       uint64_t arg5, uint32_t caller_id);

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
