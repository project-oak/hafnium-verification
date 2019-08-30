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

#include <stdint.h>

/* clang-format off */

#define SMCCC_CALL_TYPE_MASK  0x80000000
#define SMCCC_YIELDING_CALL   0x00000000
#define SMCCC_FAST_CALL       0x80000000

#define SMCCC_CONVENTION_MASK 0x40000000
#define SMCCC_32_BIT          0x00000000
#define SMCCC_64_BIT          0x40000000

#define SMCCC_SERVICE_CALL_MASK                0x3f000000
#define SMCCC_ARM_ARCHITECTURE_CALL            0x00000000
#define SMCCC_CPU_SERVICE_CALL                 0x01000000
#define SMCCC_SIP_SERVICE_CALL                 0x02000000
#define SMCCC_OEM_SERVICE_CALL                 0x03000000
#define SMCCC_STANDARD_SECURE_SERVICE_CALL     0x04000000
#define SMCCC_STANDARD_HYPERVISOR_SERVICE_CALL 0x05000000
#define SMCCC_VENDOR_HYPERVISOR_SERVICE_CALL   0x06000000

#define SMCCC_CALLER_HYPERVISOR   0x0
/*
 * TODO: Trusted application call: 0x30000000 - 0x31000000
 * TODO: Trusted OS call: 0x32000000 - 0x3f000000
 */

#define SMCCC_ERROR_UNKNOWN  (-1)

/* clang-format on */

typedef struct smc_res {
	uint64_t res0;
	uint64_t res1;
	uint64_t res2;
	uint64_t res3;
} smc_res_t;

smc_res_t smc32(uint32_t func, uint32_t arg0, uint32_t arg1, uint32_t arg2,
		uint32_t arg3, uint32_t arg4, uint32_t arg5,
		uint32_t caller_id);

smc_res_t smc64(uint32_t func, uint64_t arg0, uint64_t arg1, uint64_t arg2,
		uint64_t arg3, uint64_t arg4, uint64_t arg5,
		uint32_t caller_id);

smc_res_t smc_forward(uint32_t func, uint64_t arg0, uint64_t arg1,
		      uint64_t arg2, uint64_t arg3, uint64_t arg4,
		      uint64_t arg5, uint32_t caller_id);
