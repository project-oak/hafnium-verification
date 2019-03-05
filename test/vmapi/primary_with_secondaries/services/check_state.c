/*
 * Copyright 2018 Google LLC
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
#include "hf/arch/vm/state.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

void send_with_retry(uint32_t vm_id, size_t size)
{
	int64_t res;

	do {
		res = hf_mailbox_send(vm_id, size, false);
	} while (res == -1);
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

	for (i = 0; i < 100000; i++) {
		/*
		 * We store the expected/actual values in volatile static
		 * variables to avoid relying on registers that may have been
		 * modified by the hypervisor.
		 */
		expected = i;
		per_cpu_ptr_set(expected);
		send_with_retry(HF_PRIMARY_VM_ID, 0);
		actual = per_cpu_ptr_get();
		ok &= expected == actual;
	}

	/* Send two replies, one for each physical CPU. */
	memcpy(SERVICE_SEND_BUFFER(), &ok, sizeof(ok));
	send_with_retry(HF_PRIMARY_VM_ID, sizeof(ok));
	send_with_retry(HF_PRIMARY_VM_ID, sizeof(ok));
}
