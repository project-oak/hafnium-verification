/*
 * Copyright 2018 The Hafnium Authors.
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
	res.sleep.ns = HF_SLEEP_INDEFINITE;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0xffffffffffffff02));
}

/**
 * Encoding wait-for-interrupt response with too large sleep duration will drop
 * the top octet.
 */
TEST(abi, hf_vcpu_run_return_encode_wait_for_interrupt_sleep_too_long)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_WAIT_FOR_INTERRUPT;
	res.sleep.ns = 0xcc22888888888888;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0x2288888888888802));
}

/**
 * Decode a wait-for-interrupt response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_wait_for_interrupt)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1234abcdbadb0102);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_WAIT_FOR_INTERRUPT));
	EXPECT_THAT(res.sleep.ns, Eq(0x1234abcdbadb01));
}

/**
 * Encode wait-for-message response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_wait_for_message)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_WAIT_FOR_MESSAGE;
	res.sleep.ns = HF_SLEEP_INDEFINITE;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0xffffffffffffff03));
}

/**
 * Encoding wait-for-message response with too large sleep duration will drop
 * the top octet.
 */
TEST(abi, hf_vcpu_run_return_encode_wait_for_message_sleep_too_long)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_WAIT_FOR_MESSAGE;
	res.sleep.ns = 0xaa99777777777777;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0x9977777777777703));
}

/**
 * Decode a wait-for-message response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_wait_for_message)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x12347654badb0103);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_WAIT_FOR_MESSAGE));
	EXPECT_THAT(res.sleep.ns, Eq(0x12347654badb01));
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
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0x12345678abcd0004));
}

/**
 * Decode a wake up response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_wake_up)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0xbeefd00df00daf04);
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
	res.message.vm_id = 0xf007;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(0x0000000000f00705));
}

/**
 * Decode a wake up response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_message)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1123581314916205);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_MESSAGE));
	EXPECT_THAT(res.message.vm_id, Eq(0x9162));
}

/**
 * Encode a 'notify waiters' response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_notify_waiters)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_NOTIFY_WAITERS;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(6));
}

/**
 * Decode a 'notify waiters' response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_notify_waiters)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1a1a1a1a2b2b2b06);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_NOTIFY_WAITERS));
}

/**
 * Encode an aborted response without leaking.
 */
TEST(abi, hf_vcpu_run_return_encode_aborted)
{
	struct hf_vcpu_run_return res = dirty_vcpu_run_return();
	res.code = HF_VCPU_RUN_ABORTED;
	EXPECT_THAT(hf_vcpu_run_return_encode(res), Eq(7));
}

/**
 * Decode an aborted response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_aborted)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x31dbac4810fbc507);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_ABORTED));
}

} /* namespace */
