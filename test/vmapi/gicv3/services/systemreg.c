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

#include "hf/arch/cpu.h"
#include "hf/arch/vm/events.h"
#include "hf/arch/vm/interrupts_gicv3.h"
#include "hf/arch/vm/timer.h"

#include "hf/dlog.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "common.h"
#include "hftest.h"

/*
 * Secondary VM that tries to access GICv3 system registers.
 */

TEST_SERVICE(read_systemreg_ctlr)
{
	/* Reading ICC_CTLR_EL1 should trap and abort the VM. */
	dlog("ICC_CTLR_EL1=%#x\n", read_msr(ICC_CTLR_EL1));
	FAIL("Reading ICC_CTLR_EL1 didn't trap.");
}

TEST_SERVICE(write_systemreg_ctlr)
{
	/* Writing ICC_CTLR_EL1 should trap and abort the VM. */
	write_msr(ICC_CTLR_EL1, 0);
	FAIL("Writing ICC_CTLR_EL1 didn't trap.");
}

TEST_SERVICE(write_systemreg_sre)
{
	ASSERT_EQ(read_msr(ICC_SRE_EL1), 0x7);
	/*
	 * Writing ICC_SRE_EL1 should either trap and abort the VM or be
	 * ignored.
	 */
	write_msr(ICC_SRE_EL1, 0x0);
	ASSERT_EQ(read_msr(ICC_SRE_EL1), 0x7);
	write_msr(ICC_SRE_EL1, 0xffffffff);
	ASSERT_EQ(read_msr(ICC_SRE_EL1), 0x7);
	spci_yield();
}
