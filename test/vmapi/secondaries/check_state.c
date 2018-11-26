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

#include <stdalign.h>
#include <stdint.h>

#include "hf/arch/vm/state.h"

#include "hf/mm.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

alignas(4096) uint8_t kstack[4096];

static alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
static alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];

static hf_ipaddr_t send_page_addr = (hf_ipaddr_t)send_page;
static hf_ipaddr_t recv_page_addr = (hf_ipaddr_t)recv_page;

void send_with_retry(uint32_t vm_id, size_t size)
{
	int64_t res;

	do {
		res = hf_mailbox_send(vm_id, size);
	} while (res == -1);
}

/**
 * This VM repeatedly takes the following steps: sets the per-cpu pointer to
 * some value, makes a hypervisor call, check that the value is still what it
 * was set to.
 *
 * This loop helps detect bugs where the hypervisor inadvertently destroys
 * state.
 *
 * At the end of its iterations, the VM reports the result to the primary VM,
 * which then fails or succeeds the test.
 */
void kmain(void)
{
	size_t i;
	bool ok = true;
	static volatile uintptr_t expected;
	static volatile uintptr_t actual;

	hf_vm_configure(send_page_addr, recv_page_addr);
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
	memcpy(send_page, &ok, sizeof(ok));
	send_with_retry(HF_PRIMARY_VM_ID, sizeof(ok));
	send_with_retry(HF_PRIMARY_VM_ID, sizeof(ok));
}
