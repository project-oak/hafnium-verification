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

#include "hf/arch/std.h"
#include "hf/arch/vm/registers.h"

#include "hf/spci.h"

#include "vmapi/hf/call.h"

#include "../msr.h"
#include "primary_with_secondary.h"
#include "test/hftest.h"
#include "test/vmapi/spci.h"

/**
 * Test that floating point registers are saved and restored by
 * filling them with one value here and a different value in the
 * service.
 */
TEST(floating_point, fp_fill)
{
	const double first = 1.2;
	const double second = -2.3;
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	fill_fp_registers(first);
	SERVICE_SELECT(SERVICE_VM1, "fp_fill", mb.send);
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
	EXPECT_EQ(check_fp_register(first), true);

	fill_fp_registers(second);
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
	EXPECT_EQ(check_fp_register(second), true);
}

/**
 * Test that the floating point control register is restored correctly
 * on full context switch when needed by changing it in the service.
 */
TEST(floating_point, fp_fpcr)
{
	uintreg_t value = 0;
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	EXPECT_EQ(read_msr(fpcr), value);

	SERVICE_SELECT(SERVICE_VM1, "fp_fpcr", mb.send);
	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
	EXPECT_EQ(read_msr(fpcr), value);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
	EXPECT_EQ(read_msr(fpcr), value);
}
