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

#include "hf/arch/vm/power_mgmt.h"

#include "hf/mm.h"
#include "hf/spinlock.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

alignas(PAGE_SIZE) static char tx[PAGE_SIZE];
alignas(PAGE_SIZE) static char rx[PAGE_SIZE];

struct state {
	volatile bool done;
	struct spinlock lock;
};

/**
 * Releases the lock passed in, then spins reading the rx buffer.
 */
static void rx_reader(uintptr_t arg)
{
	struct state *s = (struct state *)arg;
	sl_unlock(&s->lock);

	while (!s->done) {
		*(volatile char *)(&rx[0]);
	}

	sl_unlock(&s->lock);
}

/**
 * Forces a spurious fault and check that Hafnium recovers from it.
 */
TEST(faults, spurious_due_to_configure)
{
	struct state s;
	alignas(4096) static uint8_t other_stack[4096];

	sl_init(&s.lock);
	s.done = false;

	/* Start secondary cpu while holding lock. */
	sl_lock(&s.lock);
	EXPECT_EQ(
		hftest_cpu_start(hftest_get_cpu_id(1), other_stack,
				 sizeof(other_stack), rx_reader, (uintptr_t)&s),
		true);

	/* Wait for CPU to release the lock. */
	sl_lock(&s.lock);

	/* Configure the VM's buffers. */
	EXPECT_EQ(hf_vm_configure((hf_ipaddr_t)&tx[0], (hf_ipaddr_t)&rx[0]), 0);

	/* Tell other CPU to stop and wait for it. */
	s.done = true;
	sl_lock(&s.lock);
}
