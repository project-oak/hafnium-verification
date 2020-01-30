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

#include <stdalign.h>
#include <stdint.h>

#include "hf/arch/vm/power_mgmt.h"

#include "hf/dlog.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"
#include "vmapi/hf/spci.h"

#include "../psci.h"
#include "primary_with_secondary.h"
#include "test/hftest.h"

#define ARG_VALUE 42

/*
 * Secondary VM that starts a second vCPU and then sends messages from both.
 */

alignas(4096) static char stack[4096];

/** Send a message back to the primary. */
void send_message(const char *message, uint32_t size)
{
	memcpy_s(SERVICE_SEND_BUFFER(), SPCI_MSG_PAYLOAD_MAX, message, size);

	ASSERT_EQ(spci_msg_send(hf_vm_get_id(), HF_PRIMARY_VM_ID, size, 0).func,
		  SPCI_SUCCESS_32);
}

/**
 * Entry point of the second vCPU.
 */
static void vm_cpu_entry(uintptr_t arg)
{
	ASSERT_EQ(arg, ARG_VALUE);

	/* Check that vCPU statuses are as expected. */
	ASSERT_EQ(arch_cpu_status(0), POWER_STATUS_ON);
	ASSERT_EQ(arch_cpu_status(1), POWER_STATUS_ON);

	dlog("Secondary second vCPU started.\n");
	send_message("vCPU 1", sizeof("vCPU 1"));
	dlog("Secondary second vCPU finishing\n");
}

TEST_SERVICE(smp)
{
	/* Check that vCPU statuses are as expected. */
	ASSERT_EQ(arch_cpu_status(0), POWER_STATUS_ON);
	ASSERT_EQ(arch_cpu_status(1), POWER_STATUS_OFF);

	/* Start second vCPU. */
	dlog("Secondary starting second vCPU.\n");
	ASSERT_TRUE(hftest_cpu_start(1, stack, sizeof(stack), vm_cpu_entry,
				     ARG_VALUE));
	dlog("Secondary started second vCPU.\n");

	/* Check that vCPU statuses are as expected. */
	ASSERT_EQ(arch_cpu_status(0), POWER_STATUS_ON);
	ASSERT_EQ(arch_cpu_status(1), POWER_STATUS_ON);

	send_message("vCPU 0", sizeof("vCPU 0"));
}
