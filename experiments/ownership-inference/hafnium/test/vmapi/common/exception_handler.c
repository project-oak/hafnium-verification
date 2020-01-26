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

#include "hf/dlog.h"

#include "vmapi/hf/call.h"

#include "../msr.h"
#include "sysregs.h"
#include "test/hftest.h"

/**
 * Tracks the number of times the exception handler has been invoked.
 */
static int exception_handler_exception_count = 0;

/**
 * Sends the number of exceptions handled to the Primary VM.
 */
void exception_handler_send_exception_count(void)
{
	void *send_buf = SERVICE_SEND_BUFFER();

	dlog("Sending exception_count %d to primary VM\n",
	     exception_handler_exception_count);
	memcpy_s(send_buf, SPCI_MSG_PAYLOAD_MAX,
		 (const void *)&exception_handler_exception_count,
		 sizeof(exception_handler_exception_count));
	EXPECT_EQ(spci_msg_send(hf_vm_get_id(), HF_PRIMARY_VM_ID,
				sizeof(exception_handler_exception_count), 0)
			  .func,
		  SPCI_SUCCESS_32);
}

/**
 * Receives the number of exceptions handled.
 */
int exception_handler_receive_exception_count(
	const struct spci_value *send_res,
	const struct spci_memory_region *recv_buf)
{
	int exception_count = *((const int *)recv_buf);

	EXPECT_EQ(send_res->func, SPCI_MSG_SEND_32);
	EXPECT_EQ(spci_msg_send_size(*send_res), sizeof(exception_count));
	EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);
	return exception_count;
}

/**
 * EL1 exception handler to use in unit test VMs.
 * Skips the instruction that triggered the exception.
 */
bool exception_handler_skip_instruction(void)
{
	dlog("%s function is triggered!\n", __func__);
	++exception_handler_exception_count;

	/* Skip instruction that triggered the exception. */
	uint64_t next_pc = read_msr(elr_el1);
	next_pc += 4UL;
	write_msr(elr_el1, next_pc);

	/* Indicate that elr_el1 should not be restored. */
	return true;
}

/**
 * EL1 exception handler to use in unit test VMs.
 * Yields control back to the hypervisor and sends the number of exceptions.
 */
static bool exception_handler_yield(void)
{
	dlog("%s function is triggered!\n", __func__);
	++exception_handler_exception_count;

	exception_handler_send_exception_count();

	/* Indicate that elr_el1 should not be restored. */
	return true;
}

/**
 * EL1 exception handler to use in unit test VMs.
 * Yields control back to the hypervisor and sends the number of exceptions.
 * Asserts that the Exception Class is Unknown.
 */
bool exception_handler_yield_unknown(void)
{
	uintreg_t esr_el1 = read_msr(ESR_EL1);
	EXPECT_EQ(GET_ESR_EC(esr_el1), EC_UNKNOWN);
	return exception_handler_yield();
}

/**
 * EL1 exception handler to use in unit test VMs.
 * Yields control back to the hypervisor and sends the number of exceptions.
 * Asserts that the Exception Class is Data Abort (same EL).
 */
bool exception_handler_yield_data_abort(void)
{
	uintreg_t esr_el1 = read_msr(ESR_EL1);
	EXPECT_EQ(GET_ESR_EC(esr_el1), EC_DATA_ABORT_SAME_EL);
	return exception_handler_yield();
}

/**
 * EL1 exception handler to use in unit test VMs.
 * Yields control back to the hypervisor and sends the number of exceptions.
 * Asserts that the Exception Class is Instruction Abort (same EL).
 */
bool exception_handler_yield_instruction_abort(void)
{
	uintreg_t esr_el1 = read_msr(ESR_EL1);
	EXPECT_EQ(GET_ESR_EC(esr_el1), EC_INSTRUCTION_ABORT_SAME_EL);
	return exception_handler_yield();
}

/**
 * Returns the number of times the instruction handler was invoked.
 */
int exception_handler_get_num(void)
{
	return exception_handler_exception_count;
}

/**
 * Resets the number of exceptions counter;
 */
void exception_handler_reset(void)
{
	exception_handler_exception_count = 0;
}
