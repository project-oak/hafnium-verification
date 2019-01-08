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

extern "C" {
#include "vmapi/hf/abi.h"
}

#include <gmock/gmock.h>

namespace
{
using ::testing::Eq;

/**
 * Simulate an uninitialized hf_vcpu_run_return so it can be detected if any
 * uninitialized fields make their way into the encoded form which would
 * indicate a data leak.
 */
struct hf_vcpu_run_return dirty_vcpu_run_return()
{
	struct hf_vcpu_run_return res;
	memset(&res, 0xc5, sizeof(res));
	return res;
}

/**
 * Simulate an uninitialized hf_mailbox_receive_return so it can be detected if
 * any uninitialized fields make their way into the encoded form which would
 * indicate a data leak.
 */
struct hf_mailbox_receive_return dirty_mailbox_receive_return()
{
	struct hf_mailbox_receive_return res;
	memset(&res, 0xc5, sizeof(res));
	return res;
}

/**
 * Encode a preempted response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_preempted)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_PREEMPTED;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0));
}

/**
 * Decode a preempted response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_preempted)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1a1a1a1a2b2b2b00);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_PREEMPTED));
}

/**
 * Encode a yield response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_yield)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_YIELD;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(1));
}

/**
 * Decode a yield response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_yield)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1a1a1a1a2b2b2b01);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_YIELD));
}

/**
 * Encode wait-for-interrupt response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_wait_for_interrupt)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_WAIT_FOR_INTERRUPT;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(2));
}

/**
 * Decode a wait-for-interrupt response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_wait_for_interrupt)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1234abcdbadb0102);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_WAIT_FOR_INTERRUPT));
}

/**
 * Encode wake up response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_wake_up)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_WAKE_UP;
	res.wake_up.vm_id = 0x12345678;
	res.wake_up.vcpu = 0xabcd;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0x12345678abcd0003));
}

/**
 * Decode a wake up response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_wake_up)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0xbeefd00df00daf03);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_WAKE_UP));
	EXPECT_THAT(res.wake_up.vm_id, Eq(0xbeefd00d));
	EXPECT_THAT(res.wake_up.vcpu, Eq(0xf00d));
}

/**
 * Encode message response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_message)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_MESSAGE;
	res.message.size = 0xdeadbeef;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0xdeadbeef00000004));
}

/**
 * Decode a wake up response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_message)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1123581314916204);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_MESSAGE));
	EXPECT_THAT(res.message.size, Eq(0x11235813));
}

/**
 * Encode sleep response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_sleep)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_SLEEP;
	res.sleep.ns = 0xcafed00dfeeded;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0xcafed00dfeeded05));
}

/**
 * Encoding a sleep response with too large a sleep duration will drop the top
 * octet.
 */
TEST(abi, hf_vcpu_run_return_encode_sleep_too_long)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_SLEEP;
	res.sleep.ns = 0xcc88888888888888;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0x8888888888888805));
}

/**
 * Decode a sleep response.
 */
TEST(abi, hf_vcpu_run_return_decode_sleep)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1a2b3c4d5e6f7705);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_SLEEP));
	EXPECT_THAT(res.sleep.ns, Eq(0x1a2b3c4d5e6f77));
}

/**
 * Encode a mailbox receive response without leaking.
 */
TEST(abi, hf_mailbox_receive_return_encode)
{
	struct hf_mailbox_receive_return res = dirty_mailbox_receive_return();
	res.vm_id = 0x12345678;
	res.size = 0xaabbccdd;
	EXPECT_THAT(hf_mailbox_receive_return_encode(res),
		    Eq(0xaabbccdd12345678));
}

/**
 * Decode a mailbox receive response.
 */
TEST(abi, hf_mailbox_receive_return_decode)
{
	struct hf_mailbox_receive_return res =
		hf_mailbox_receive_return_decode(0X8badf00d00ddba11);
	EXPECT_THAT(res.vm_id, Eq(0X00ddba11));
	EXPECT_THAT(res.size, Eq(0x8badf00d));
}

} /* namespace */
