#include <assert.h>
#include <stdalign.h>
#include <stdint.h>

#include "hf/mm.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

static alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
static alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];
static_assert(sizeof(send_page) == PAGE_SIZE, "Send page is not a page.");
static_assert(sizeof(recv_page) == PAGE_SIZE, "Recv page is not a page.");

static hf_ipaddr_t send_page_addr = (hf_ipaddr_t)send_page;
static hf_ipaddr_t recv_page_addr = (hf_ipaddr_t)recv_page;

#define ECHO_VM_ID 1

/**
 * Confirm there is 1 secondary VM.
 */
TEST(hf_vm_get_count, one_secondary_vm)
{
	EXPECT_EQ(hf_vm_get_count(), 2);
}

/**
 * Confirm there that secondary VM has 1 VCPU.
 */
TEST(hf_vcpu_get_count, secondary_has_one_vcpu)
{
	EXPECT_EQ(hf_vcpu_get_count(1), 1);
}

/**
 * Confirm it is an error to query how many VCPUs are assigned to a nonexistent
 * secondary VM.
 */
TEST(hf_vcpu_get_count, large_invalid_vm_index)
{
	EXPECT_EQ(hf_vcpu_get_count(0xffffffff), -1);
}

/**
 * The configured send/receive addresses can't be unaligned.
 */
TEST(hf_vm_configure, fails_with_unaligned_pointer)
{
	uint8_t maybe_aligned[2];
	hf_ipaddr_t unaligned_addr = (hf_ipaddr_t)&maybe_aligned[1];
	hf_ipaddr_t aligned_addr = (hf_ipaddr_t)send_page;

	/* Check the the address is unaligned. */
	ASSERT_EQ(unaligned_addr & 1, 1);

	EXPECT_EQ(hf_vm_configure(aligned_addr, unaligned_addr), -1);
	EXPECT_EQ(hf_vm_configure(unaligned_addr, aligned_addr), -1);
	EXPECT_EQ(hf_vm_configure(unaligned_addr, unaligned_addr), -1);
}

/**
 * The configured send/receive addresses can't be the same page.
 */
TEST(hf_vm_configure, fails_with_same_page)
{
	EXPECT_EQ(hf_vm_configure(send_page_addr, send_page_addr), -1);
	EXPECT_EQ(hf_vm_configure(recv_page_addr, recv_page_addr), -1);
}

/**
 * The configuration of the send/receive addresses can only happen once.
 */
TEST(hf_vm_configure, fails_if_already_succeeded)
{
	EXPECT_EQ(hf_vm_configure(send_page_addr, recv_page_addr), 0);
	EXPECT_EQ(hf_vm_configure(send_page_addr, recv_page_addr), -1);
}

/**
 * The configuration of the send/receive address is successful with valid
 * arguments.
 */
TEST(hf_vm_configure, succeeds)
{
	EXPECT_EQ(hf_vm_configure(send_page_addr, recv_page_addr), 0);
}

/**
 * Send and receive the same message from the echo VM.
 */
TEST(mailbox, echo)
{
	const char message[] = "Echo this back to me!";

	/* Configure mailbox pages. */
	EXPECT_EQ(hf_vm_configure(send_page_addr, recv_page_addr), 0);
	EXPECT_EQ(hf_vcpu_run(ECHO_VM_ID, 0),
		  HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_WAIT_FOR_INTERRUPT, 0, 0));

	/* Set the message, echo it and check it didn't change. */
	memcpy(send_page, message, sizeof(message));
	EXPECT_EQ(hf_mailbox_send(ECHO_VM_ID, sizeof(message)), 0);
	EXPECT_EQ(
		hf_vcpu_run(ECHO_VM_ID, 0),
		HF_VCPU_RUN_RESPONSE(HF_VCPU_RUN_MESSAGE, 0, sizeof(message)));
	EXPECT_EQ(memcmp(recv_page, message, sizeof(message)), 0);
	EXPECT_EQ(hf_mailbox_clear(), 0);
}
