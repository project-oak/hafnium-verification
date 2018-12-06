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

#pragma once

#include "hf/types.h"

enum hf_vcpu_run_code {
	/**
	 * The vCPU has been preempted but still has work to do. If the
	 * scheduling quantum has not expired, the scheduler MUST call
	 * `hf_vcpu_run` on the vCPU to allow it to continue.
	 */
	HF_VCPU_RUN_PREEMPTED,

	/**
	 * The vCPU has voluntarily yielded the CPU. The scheduler SHOULD take a
	 * scheduling decision to give cycles to those that need them but MUST
	 * call `hf_vcpu_run` on the vCPU at a later point.
	 */
	HF_VCPU_RUN_YIELD,

	/**
	 * The vCPU is blocked waiting for an interrupt. The scheduler MUST take
	 * it off the run queue and not call `hf_vcpu_run` on the vCPU until it
	 * has injected an interrupt, sent it a message, or got a
	 * `HF_VCPU_RUN_WAKE_UP` for it from another vCPU.
	 */
	HF_VCPU_RUN_WAIT_FOR_INTERRUPT,

	/**
	 * The vCPU would like `hf_vcpu_run` to be called on another vCPU,
	 * specified by `hf_vcpu_run_return.wake_up`. The scheduler MUST
	 * either wake the vCPU in question up if it is blocked, or preempt and
	 * re-run it if it is already running somewhere. This gives Hafnium a
	 * chance to update any CPU state which might have changed.
	 */
	HF_VCPU_RUN_WAKE_UP,

	/**
	 * A new message is available for the scheduler VM, as specified by
	 * `hf_vcpu_run_return.message`.
	 */
	HF_VCPU_RUN_MESSAGE,

	/**
	 * Like `HF_VCPU_RUN_WAIT_FOR_INTERRUPT`, but for a limited amount of
	 * time, specified by `hf_vcpu_run_return.sleep`. After at least that
	 * amount of time has passed, or any of the events listed for
	 * `HF_VCPU_RUN_WAIT_FOR_INTERRUPT` occur, the scheduler MUST call
	 * `hf_vcpu_run` on it again.
	 */
	HF_VCPU_RUN_SLEEP,

	/**
	 * The vCPU has made the mailbox writable and there are pending waiters.
	 * The scheduler MUST call hf_mailbox_waiter_get() repeatedly and notify
	 * all waiters by injecting an HF_MAILBOX_WRITABLE_INTID interrupt.
	 */
	HF_VCPU_RUN_NOTIFY_WAITERS,
};

struct hf_vcpu_run_return {
	enum hf_vcpu_run_code code;
	union {
		struct {
			uint32_t vm_id;
			uint16_t vcpu;
		} wake_up;
		struct {
			uint32_t size;
		} message;
		struct {
			uint64_t ns;
		} sleep;
	};
};

struct hf_mailbox_receive_return {
	uint32_t vm_id;
	uint32_t size;
};

enum hf_share {
	/**
	 * Relinquish ownership and access to the memory and pass them to the
	 * recipient.
	 */
	HF_MEMORY_GIVE,

	/**
	 * Retain ownership of the memory but relinquish access to the
	 * recipient.
	 */
	HF_MEMORY_LEND,

	/**
	 * Retain ownership and access but additionally allow access to the
	 * recipient.
	 */
	HF_MEMORY_SHARE,
};

/**
 * Encode an hf_vcpu_run_return struct in the 64-bit packing ABI.
 */
static inline uint64_t hf_vcpu_run_return_encode(struct hf_vcpu_run_return res)
{
	uint64_t ret = res.code & 0xff;

	switch (res.code) {
	case HF_VCPU_RUN_WAKE_UP:
		ret |= (uint64_t)res.wake_up.vm_id << 32;
		ret |= (uint64_t)res.wake_up.vcpu << 16;
		break;
	case HF_VCPU_RUN_MESSAGE:
		ret |= (uint64_t)res.message.size << 32;
		break;
	case HF_VCPU_RUN_SLEEP:
		ret |= res.sleep.ns << 8;
		break;
	default:
		break;
	}

	return ret;
}

/**
 * Decode an hf_vcpu_run_return struct from the 64-bit packing ABI.
 */
static inline struct hf_vcpu_run_return hf_vcpu_run_return_decode(uint64_t res)
{
	struct hf_vcpu_run_return ret = {
		.code = (enum hf_vcpu_run_code)(res & 0xff),
	};

	/* Some codes include more data. */
	switch (ret.code) {
	case HF_VCPU_RUN_WAKE_UP:
		ret.wake_up.vm_id = res >> 32;
		ret.wake_up.vcpu = (res >> 16) & 0xffff;
		break;
	case HF_VCPU_RUN_MESSAGE:
		ret.message.size = res >> 32;
		break;
	case HF_VCPU_RUN_SLEEP:
		ret.sleep.ns = res >> 8;
		break;
	default:
		break;
	}

	return ret;
}

/**
 * Encode an hf_mailbox_receive_return struct in the 64-bit packing ABI.
 */
static inline uint64_t hf_mailbox_receive_return_encode(
	struct hf_mailbox_receive_return res)
{
	return res.vm_id | ((uint64_t)res.size << 32);
}

/**
 * Decode an hf_mailbox_receive_return struct from the 64-bit packing ABI.
 */
static inline struct hf_mailbox_receive_return hf_mailbox_receive_return_decode(
	uint64_t res)
{
	return (struct hf_mailbox_receive_return){
		.vm_id = (uint32_t)(res & 0xffffffff),
		.size = (uint32_t)(res >> 32),
	};
}
