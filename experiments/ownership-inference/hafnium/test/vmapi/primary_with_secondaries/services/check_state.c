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

#include "test/hftest.h"

void send_with_retry(spci_vm_id_t sender_vm_id, spci_vm_id_t target_vm_id,
		     uint32_t size)
{
	struct spci_value res;

	do {
		res = spci_msg_send(sender_vm_id, target_vm_id, size, 0);
	} while (res.func != SPCI_SUCCESS_32);
}

/**
 * This service repeatedly takes the following steps: sets the per-CPU pointer
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

	for (i = 0; i < 100000; i++) {
		/*
		 * We store the expected/actual values in volatile static
		 * variables to avoid relying on registers that may have been
		 * modified by the hypervisor.
		 */
		expected = i;
		per_cpu_ptr_set(expected);
		send_with_retry(hf_vm_get_id(), HF_PRIMARY_VM_ID, 0);
		actual = per_cpu_ptr_get();
		ok &= expected == actual;
	}

	/* Send two replies, one for each physical CPU. */
	memcpy_s(SERVICE_SEND_BUFFER(), SPCI_MSG_PAYLOAD_MAX, &ok, sizeof(ok));
	send_with_retry(hf_vm_get_id(), HF_PRIMARY_VM_ID, sizeof(ok));
	send_with_retry(hf_vm_get_id(), HF_PRIMARY_VM_ID, sizeof(ok));
}
