#include <assert.h>
#include <stdalign.h>
#include <stdint.h>

#include "../hf_test.h"
#include "mm.h"
#include "vmapi/hf/call.h"

alignas(4096) uint8_t kstack[4096];

alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];
static_assert(sizeof(send_page) == PAGE_SIZE, "Send page is not a page.");
static_assert(sizeof(recv_page) == PAGE_SIZE, "Recv page is not a page.");

TEST(vm_get_count)
{
	EXPECT_EQ(hf_vm_get_count(), 1);
}

TEST(vcpu_get_count_when_no_secondary_vm)
{
	EXPECT_EQ(hf_vcpu_get_count(0), 1);
}

TEST(vcpu_get_count_for_large_invalid_vm_index)
{
	EXPECT_EQ(hf_vcpu_get_count(0xffffffff), -1);
}

TEST(vm_configure_fails_with_unaligned_pointer)
{
	uint8_t maybe_aligned[2];
	hf_ipaddr_t unaligned_addr = (hf_ipaddr_t)&maybe_aligned[1];
	hf_ipaddr_t aligned_addr = (hf_ipaddr_t)&send_page;

	/* Check the the address is unaligned. */
	ASSERT_EQ(unaligned_addr & 1, 1);

	EXPECT_EQ(hf_vm_configure(aligned_addr, unaligned_addr), -1);
	EXPECT_EQ(hf_vm_configure(unaligned_addr, aligned_addr), -1);
	EXPECT_EQ(hf_vm_configure(unaligned_addr, unaligned_addr), -1);
}

TEST(vm_configure_fails_with_same_page)
{
	EXPECT_EQ(
		hf_vm_configure((hf_ipaddr_t)send_page, (hf_ipaddr_t)send_page),
		-1);
	EXPECT_EQ(
		hf_vm_configure((hf_ipaddr_t)recv_page, (hf_ipaddr_t)recv_page),
		-1);
}

TEST(vm_configure)
{
	EXPECT_EQ(
		hf_vm_configure((hf_ipaddr_t)send_page, (hf_ipaddr_t)recv_page),
		0);
}

TEST(vm_configure_fails_if_already_succeeded)
{
	EXPECT_EQ(
		hf_vm_configure((hf_ipaddr_t)send_page, (hf_ipaddr_t)recv_page),
		-1);
}

void kmain(void)
{
	RUN_TEST(vm_get_count);
	RUN_TEST(vcpu_get_count_when_no_secondary_vm);
	RUN_TEST(vcpu_get_count_for_large_invalid_vm_index);

	/* TODO: the order matters as the configuration can only be set once.
	 * We'll need to work out how to deal with this better in the tests. */
	RUN_TEST(vm_configure_fails_with_unaligned_pointer);
	RUN_TEST(vm_configure_fails_with_same_page);
	RUN_TEST(vm_configure);
	RUN_TEST(vm_configure_fails_if_already_succeeded);
}
