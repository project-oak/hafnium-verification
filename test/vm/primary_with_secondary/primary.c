#include <stdint.h>

#include "../hf_test.h"
#include "vmapi/hf/call.h"

uint8_t kstack[4096] __attribute__((aligned(4096)));

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

void kmain(void)
{
	RUN_TEST(vm_get_count);
	RUN_TEST(vcpu_get_count_when_no_secondary_vm);
	RUN_TEST(vcpu_get_count_for_large_invalid_vm_index);
}
