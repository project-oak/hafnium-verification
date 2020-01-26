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

#include "hf/arch/vm/interrupts.h"

#include "hf/mm.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "test/hftest.h"
#include "test/vmapi/exception_handler.h"

/*
 * This must match the size specified for services1 in
 * //test/vmapi/primary_with_secondaries:primary_with_secondaries_test.
 */
#define SECONDARY_MEMORY_SIZE 1048576

extern uint8_t volatile text_begin[];

TEST_SERVICE(boot_memory)
{
	uint8_t checksum = 0;

	/* Check that the size passed in by Hafnium is what is expected. */
	ASSERT_EQ(SERVICE_MEMORY_SIZE(), SECONDARY_MEMORY_SIZE);

	/*
	 * Check that we can read all memory up to the given size. Calculate a
	 * basic checksum and check that it is non-zero, as a double-check that
	 * we are actually reading something.
	 */
	for (size_t i = 0; i < SERVICE_MEMORY_SIZE(); ++i) {
		checksum += text_begin[i];
	}
	ASSERT_NE(checksum, 0);
	dlog("Checksum of all memory is %d\n", checksum);

	spci_yield();
}

TEST_SERVICE(boot_memory_underrun)
{
	exception_setup(NULL, exception_handler_yield_data_abort);
	/*
	 * Try to read memory below the start of the image. This should result
	 * in the VM trapping and yielding.
	 */
	dlog("Read memory below limit: %d\n", text_begin[-1]);
	FAIL("Managed to read memory below limit");
}

TEST_SERVICE(boot_memory_overrun)
{
	exception_setup(NULL, exception_handler_yield_data_abort);
	/*
	 * Try to read memory above the limit defined by memory_size. This
	 * should result in the VM trapping and yielding.
	 */
	dlog("Read memory above limit: %d\n",
	     text_begin[SERVICE_MEMORY_SIZE()]);
	FAIL("Managed to read memory above limit");
}
