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

#include "sysregs.h"

#include "hf/arch/vm/interrupts.h"

#include "primary_with_secondary.h"
#include "test/vmapi/exception_handler.h"
#include "test/vmapi/spci.h"

SET_UP(sysregs)
{
	exception_setup(NULL, exception_handler_skip_instruction);
}

/**
 * Test that accessing LOR registers would inject an exception.
 */
TEST(sysregs, lor_exception)
{
	EXPECT_EQ(hf_vm_get_id(), HF_PRIMARY_VM_ID);
	TRY_READ(MSR_LORC_EL1);

	EXPECT_EQ(exception_handler_get_num(), 1);
}
