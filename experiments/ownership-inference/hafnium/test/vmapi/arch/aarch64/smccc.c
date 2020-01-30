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

#include <stdint.h>

#include "vmapi/hf/call.h"
#include "vmapi/hf/spci.h"

#include "smc.h"
#include "test/hftest.h"

static struct spci_value hvc(uint32_t func, uint64_t arg0, uint64_t arg1,
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

	__asm__ volatile(
		"hvc #0"
		: /* Output registers, also used as inputs ('+' constraint). */
		"+r"(r0), "+r"(r1), "+r"(r2), "+r"(r3), "+r"(r4), "+r"(r5),
		"+r"(r6), "+r"(r7));

	return (struct spci_value){.func = r0,
				   .arg1 = r1,
				   .arg2 = r2,
				   .arg3 = r3,
				   .arg4 = r4,
				   .arg5 = r5,
				   .arg6 = r6,
				   .arg7 = r7};
}

TEST(smccc, hf_debug_log_smc_zero_or_unchanged)
{
	struct spci_value smc_res =
		smc_forward(HF_DEBUG_LOG, '\n', 0x2222222222222222,
			    0x3333333333333333, 0x4444444444444444,
			    0x5555555555555555, 0x6666666666666666, 0x77777777);

	EXPECT_EQ(smc_res.func, 0);
	EXPECT_EQ(smc_res.arg1, '\n');
	EXPECT_EQ(smc_res.arg2, UINT64_C(0x2222222222222222));
	EXPECT_EQ(smc_res.arg3, UINT64_C(0x3333333333333333));
	EXPECT_EQ(smc_res.arg4, UINT64_C(0x4444444444444444));
	EXPECT_EQ(smc_res.arg5, UINT64_C(0x5555555555555555));
	EXPECT_EQ(smc_res.arg6, UINT64_C(0x6666666666666666));
	EXPECT_EQ(smc_res.arg7, UINT64_C(0x77777777));
}

TEST(smccc, hf_debug_log_hvc_zero_or_unchanged)
{
	struct spci_value smc_res =
		hvc(HF_DEBUG_LOG, '\n', 0x2222222222222222, 0x3333333333333333,
		    0x4444444444444444, 0x5555555555555555, 0x6666666666666666,
		    0x77777777);

	EXPECT_EQ(smc_res.func, 0);
	EXPECT_EQ(smc_res.arg1, '\n');
	EXPECT_EQ(smc_res.arg2, UINT64_C(0x2222222222222222));
	EXPECT_EQ(smc_res.arg3, UINT64_C(0x3333333333333333));
	EXPECT_EQ(smc_res.arg4, UINT64_C(0x4444444444444444));
	EXPECT_EQ(smc_res.arg5, UINT64_C(0x5555555555555555));
	EXPECT_EQ(smc_res.arg6, UINT64_C(0x6666666666666666));
	EXPECT_EQ(smc_res.arg7, UINT64_C(0x77777777));
}

/**
 * Checks that calling SPCI_FEATURES via an SMC works as expected.
 * The spci_features helper function uses an HVC, but an SMC should also work.
 */
TEST(smccc, spci_features_smc)
{
	struct spci_value ret;

	ret = smc32(SPCI_FEATURES_32, SPCI_VERSION_32, 0, 0, 0, 0, 0, 0);
	EXPECT_EQ(ret.func, SPCI_SUCCESS_32);
	EXPECT_EQ(ret.arg1, 0);
	EXPECT_EQ(ret.arg2, 0);
	EXPECT_EQ(ret.arg3, 0);
	EXPECT_EQ(ret.arg4, 0);
	EXPECT_EQ(ret.arg5, 0);
	EXPECT_EQ(ret.arg6, 0);
	EXPECT_EQ(ret.arg7, 0);
}
