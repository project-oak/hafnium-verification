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

#include "hf/arch/vm/events.h"
#include "hf/arch/vm/interrupts.h"
#include "hf/arch/vm/interrupts_gicv3.h"
#include "hf/arch/vm/timer.h"

#include "hf/dlog.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "common.h"
#include "test/hftest.h"
#include "test/vmapi/exception_handler.h"

/*
 * Secondary VM that tries to access GICv3 system registers.
 */

TEST_SERVICE(access_systemreg_ctlr)
{
	exception_setup(NULL, exception_handler_skip_instruction);

	/* Reading ICC_CTLR_EL1 should trap the VM. */
	read_msr(ICC_CTLR_EL1);

	/* Writing ICC_CTLR_EL1 should trap the VM. */
	write_msr(ICC_CTLR_EL1, 0);

	EXPECT_EQ(exception_handler_get_num(), 2);

	/* Yield after catching the exceptions. */
	spci_yield();
}

TEST_SERVICE(write_systemreg_sre)
{
	uintreg_t read;

	exception_setup(NULL, exception_handler_skip_instruction);

	read = read_msr(ICC_SRE_EL1);
	if (exception_handler_get_num() != 0) {
		/* If reads are trapped then writes should also be trapped. */
		ASSERT_EQ(exception_handler_get_num(), 1);
		write_msr(ICC_SRE_EL1, 0x0);
		ASSERT_EQ(exception_handler_get_num(), 2);
	} else {
		ASSERT_EQ(read, 0x7);
		/* Writing ICC_SRE_EL1 should be ignored. */
		write_msr(ICC_SRE_EL1, 0x0);
		ASSERT_EQ(read_msr(ICC_SRE_EL1), 0x7);
		write_msr(ICC_SRE_EL1, 0xffffffff);
		ASSERT_EQ(read_msr(ICC_SRE_EL1), 0x7);
	}

	spci_yield();
}
