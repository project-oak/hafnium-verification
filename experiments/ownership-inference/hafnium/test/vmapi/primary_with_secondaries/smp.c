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

#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "primary_with_secondary.h"
#include "test/hftest.h"
#include "test/vmapi/spci.h"

TEAR_DOWN(smp)
{
	EXPECT_SPCI_ERROR(spci_rx_release(), SPCI_DENIED);
}

/**
 * Run a service that starts a second vCPU, and check that both the first and
 * second vCPU send messages to us.
 */
TEST(smp, two_vcpus)
{
	const char expected_response_0[] = "vCPU 0";
	const char expected_response_1[] = "vCPU 1";
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM3, "smp", mb.send);

	/* Let the first vCPU start the second vCPU. */
	run_res = spci_run(SERVICE_VM3, 0);
	EXPECT_EQ(run_res.func, HF_SPCI_RUN_WAKE_UP);
	EXPECT_EQ(spci_vm_id(run_res), SERVICE_VM3);
	EXPECT_EQ(spci_vcpu_index(run_res), 1);

	/* Run the second vCPU and wait for a message. */
	dlog("Run second vCPU for message\n");
	run_res = spci_run(SERVICE_VM3, 1);
	EXPECT_EQ(run_res.func, SPCI_MSG_SEND_32);
	EXPECT_EQ(spci_msg_send_size(run_res), sizeof(expected_response_1));
	EXPECT_EQ(memcmp(mb.recv, expected_response_1,
			 sizeof(expected_response_1)),
		  0);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Run the first vCPU and wait for a different message. */
	dlog("Run first vCPU for message\n");
	run_res = spci_run(SERVICE_VM3, 0);
	EXPECT_EQ(run_res.func, SPCI_MSG_SEND_32);
	EXPECT_EQ(spci_msg_send_size(run_res), sizeof(expected_response_0));
	EXPECT_EQ(memcmp(mb.recv, expected_response_0,
			 sizeof(expected_response_0)),
		  0);
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);

	/* Run the second vCPU again, and expect it to turn itself off. */
	dlog("Run second vCPU for poweroff.\n");
	run_res = spci_run(SERVICE_VM3, 1);
	EXPECT_EQ(run_res.func, HF_SPCI_RUN_WAIT_FOR_INTERRUPT);
	EXPECT_EQ(run_res.arg2, SPCI_SLEEP_INDEFINITE);
}
