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
 * Decode a preempted response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_preempted)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1a1a1a1a2b2b2b00);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_PREEMPTED));
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
 * Decode a wake up response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_wake_up)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0xbeeff00daf04);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_WAKE_UP));
	EXPECT_THAT(res.wake_up.vm_id, Eq(0xbeef));
	EXPECT_THAT(res.wake_up.vcpu, Eq(0xf00d));
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
 * Decode a 'notify waiters' response ignoring the irrelevant bits.
 */
TEST(abi, hf_vcpu_run_return_decode_notify_waiters)
{
	struct hf_vcpu_run_return res =
		hf_vcpu_run_return_decode(0x1a1a1a1a2b2b2b06);
	EXPECT_THAT(res.code, Eq(HF_VCPU_RUN_NOTIFY_WAITERS));
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
