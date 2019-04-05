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

#include "hf/arch/vm/state.h"

#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

void send_with_retry()
{
	int64_t res;

	do {
		res = spci_msg_send(0);
	} while (res != SPCI_SUCCESS);
}

/**
 * This service repeatedly takes the following steps: sets the per-cpu pointer
 * to some value, makes a hypervisor call, check that the value is still what it
 * was set to.
 *
 * This loop helps detect bugs where the hypervisor inadvertently destroys
 * state.
 *
 * At the end of its iterations, the service reports the result to the primary
 * VM, which then fails or succeeds the test.
 */
TEST_SERVICE(check_state)
{
	size_t i;
	bool ok = true;
	static volatile uintptr_t expected;
	static volatile uintptr_t actual;

	spci_message_init(SERVICE_SEND_BUFFER(), 0, HF_PRIMARY_VM_ID,
			  hf_vm_get_id());

	for (i = 0; i < 100000; i++) {
		/*
		 * We store the expected/actual values in volatile static
		 * variables to avoid relying on registers that may have been
		 * modified by the hypervisor.
		 */
		expected = i;
		per_cpu_ptr_set(expected);
		send_with_retry();
		actual = per_cpu_ptr_get();
		ok &= expected == actual;
	}

	/* Send two replies, one for each physical CPU. */
	memcpy_s(SERVICE_SEND_BUFFER()->payload, SPCI_MSG_PAYLOAD_MAX, &ok,
		 sizeof(ok));
	spci_message_init(SERVICE_SEND_BUFFER(), sizeof(ok), HF_PRIMARY_VM_ID,
			  hf_vm_get_id());
	send_with_retry();
	send_with_retry();
}
