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

#include "../../src/arch/aarch64/hypervisor/perfmon.h"

#include "../../src/arch/aarch64/sysregs.h"
#include "primary_with_secondary.h"
#include "sysregs.h"
#include "test/vmapi/spci.h"

TEST(perfmon, secondary_basic)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM1, "perfmon_secondary_basic", mb.send);

	run_res = spci_run(SERVICE_VM1, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Attempts to access performance monitor registers for read, without validating
 * their value.
 */
TEST(perfmon, primary_basic)
{
	EXPECT_EQ(hf_vm_get_id(), HF_PRIMARY_VM_ID);

	TRY_READ(PMCEID0_EL0);
	TRY_READ(PMCEID1_EL0);
	TRY_READ(PMCCFILTR_EL0);
	TRY_READ(PMCR_EL0);
}

/**
 * Tests a few performance counter registers for read and write, and checks that
 * the expected value is written/read.
 */
TEST(perfmon, primary_read_write)
{
	uintreg_t pmcr_el0 = read_msr(PMCR_EL0);
	uintreg_t perf_mon_count = GET_PMCR_EL0_N(pmcr_el0);

	EXPECT_EQ(hf_vm_get_id(), HF_PRIMARY_VM_ID);

	/*
	 * Ensure that there are enough performance counters in the underlying
	 * uArch for this test to pass.
	 */
	EXPECT_GE(perf_mon_count, 4);

	TRY_WRITE_READ(PMCCNTR_EL0, 0xaaaa);

	write_msr(PMINTENCLR_EL1, 0xffff);
	CHECK_READ(PMINTENSET_EL1, 0);

	/*
	 * Enable the first and second performance counters.
	 * Bits set in PMINTENSET_EL1 can be read in PMINTENCLR_EL1.
	 */
	write_msr(PMINTENSET_EL1, 0x3);
	CHECK_READ(PMINTENCLR_EL1, 0x3);

	/*
	 * Enable the third and fourth performance counters.
	 * Writes to PMINTENSET_EL1 do not clear already set bits.
	 */
	write_msr(PMINTENSET_EL1, 0xc);
	CHECK_READ(PMINTENCLR_EL1, 0xf);
}

/**
 * Attempts to read all performance counters supported by the current CPU
 * configuration.
 */
/* NOLINTNEXTLINE(readability-function-size) */
TEST(perfmon, primary_counters)
{
	uintreg_t pmcr_el0 = read_msr(PMCR_EL0);
	uintreg_t perf_mon_count = GET_PMCR_EL0_N(pmcr_el0);

	EXPECT_EQ(hf_vm_get_id(), HF_PRIMARY_VM_ID);

	if (perf_mon_count == 0) {
		return;
	}

	switch (perf_mon_count - 1) {
	default:
		FAIL("More performance monitor registers than supported.");
	case 30:
		TRY_READ(PMEVCNTR30_EL0);
		TRY_WRITE_READ(PMEVTYPER30_EL0, 0x1);
		/* fallthrough */
	case 29:
		TRY_READ(PMEVCNTR29_EL0);
		TRY_WRITE_READ(PMEVTYPER29_EL0, 0x1);
		/* fallthrough */
	case 28:
		TRY_READ(PMEVCNTR28_EL0);
		TRY_WRITE_READ(PMEVTYPER28_EL0, 0x1);
		/* fallthrough */
	case 27:
		TRY_READ(PMEVCNTR27_EL0);
		TRY_WRITE_READ(PMEVTYPER27_EL0, 0x1);
		/* fallthrough */
	case 26:
		TRY_READ(PMEVCNTR26_EL0);
		TRY_WRITE_READ(PMEVTYPER26_EL0, 0x1);
		/* fallthrough */
	case 25:
		TRY_READ(PMEVCNTR25_EL0);
		TRY_WRITE_READ(PMEVTYPER25_EL0, 0x1);
		/* fallthrough */
	case 24:
		TRY_READ(PMEVCNTR24_EL0);
		TRY_WRITE_READ(PMEVTYPER24_EL0, 0x1);
		/* fallthrough */
	case 23:
		TRY_READ(PMEVCNTR23_EL0);
		TRY_WRITE_READ(PMEVTYPER23_EL0, 0x1);
		/* fallthrough */
	case 22:
		TRY_READ(PMEVCNTR22_EL0);
		TRY_WRITE_READ(PMEVTYPER22_EL0, 0x1);
		/* fallthrough */
	case 21:
		TRY_READ(PMEVCNTR21_EL0);
		TRY_WRITE_READ(PMEVTYPER21_EL0, 0x1);
		/* fallthrough */
	case 20:
		TRY_READ(PMEVCNTR20_EL0);
		TRY_WRITE_READ(PMEVTYPER20_EL0, 0x1);
		/* fallthrough */
	case 19:
		TRY_READ(PMEVCNTR19_EL0);
		TRY_WRITE_READ(PMEVTYPER19_EL0, 0x1);
		/* fallthrough */
	case 18:
		TRY_READ(PMEVCNTR18_EL0);
		TRY_WRITE_READ(PMEVTYPER18_EL0, 0x1);
		/* fallthrough */
	case 17:
		TRY_READ(PMEVCNTR17_EL0);
		TRY_WRITE_READ(PMEVTYPER17_EL0, 0x1);
		/* fallthrough */
	case 16:
		TRY_READ(PMEVCNTR16_EL0);
		TRY_WRITE_READ(PMEVTYPER16_EL0, 0x1);
		/* fallthrough */
	case 15:
		TRY_READ(PMEVCNTR15_EL0);
		TRY_WRITE_READ(PMEVTYPER15_EL0, 0x1);
		/* fallthrough */
	case 14:
		TRY_READ(PMEVCNTR14_EL0);
		TRY_WRITE_READ(PMEVTYPER14_EL0, 0x1);
		/* fallthrough */
	case 13:
		TRY_READ(PMEVCNTR13_EL0);
		TRY_WRITE_READ(PMEVTYPER13_EL0, 0x1);
		/* fallthrough */
	case 12:
		TRY_READ(PMEVCNTR12_EL0);
		TRY_WRITE_READ(PMEVTYPER12_EL0, 0x1);
		/* fallthrough */
	case 11:
		TRY_READ(PMEVCNTR11_EL0);
		TRY_WRITE_READ(PMEVTYPER11_EL0, 0x1);
		/* fallthrough */
	case 10:
		TRY_READ(PMEVCNTR10_EL0);
		TRY_WRITE_READ(PMEVTYPER10_EL0, 0x1);
		/* fallthrough */
	case 9:
		TRY_READ(PMEVCNTR9_EL0);
		TRY_WRITE_READ(PMEVTYPER9_EL0, 0x1);
		/* fallthrough */
	case 8:
		TRY_READ(PMEVCNTR8_EL0);
		TRY_WRITE_READ(PMEVTYPER8_EL0, 0x1);
		/* fallthrough */
	case 7:
		TRY_READ(PMEVCNTR7_EL0);
		TRY_WRITE_READ(PMEVTYPER7_EL0, 0x1);
		/* fallthrough */
	case 6:
		TRY_READ(PMEVCNTR6_EL0);
		TRY_WRITE_READ(PMEVTYPER6_EL0, 0x1);
		/* fallthrough */
	case 5:
		TRY_READ(PMEVCNTR5_EL0);
		TRY_WRITE_READ(PMEVTYPER5_EL0, 0x1);
		/* fallthrough */
	case 4:
		TRY_READ(PMEVCNTR4_EL0);
		TRY_WRITE_READ(PMEVTYPER4_EL0, 0x1);
		/* fallthrough */
	case 3:
		TRY_READ(PMEVCNTR3_EL0);
		TRY_WRITE_READ(PMEVTYPER3_EL0, 0x1);
		/* fallthrough */
	case 2:
		TRY_READ(PMEVCNTR2_EL0);
		TRY_WRITE_READ(PMEVTYPER2_EL0, 0x1);
		/* fallthrough */
	case 1:
		TRY_READ(PMEVCNTR1_EL0);
		TRY_WRITE_READ(PMEVTYPER1_EL0, 0x1);
		/* fallthrough */
	case 0:
		TRY_READ(PMEVCNTR0_EL0);
		TRY_WRITE_READ(PMEVTYPER0_EL0, 0x1);
		break;
	}
}
