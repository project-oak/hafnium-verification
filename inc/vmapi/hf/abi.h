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

#pragma once

#include "hf/types.h"

enum hf_vcpu_run_code {
	/**
	 * The vCPU has been preempted but still has work to do. If the
	 * scheduling quantum has not expired, the scheduler MUST call
	 * `hf_vcpu_run` on the vCPU to allow it to continue.
	 */
	HF_VCPU_RUN_PREEMPTED = 0,

	/**
	 * The vCPU has voluntarily yielded the CPU. The scheduler SHOULD take a
	 * scheduling decision to give cycles to those that need them but MUST
	 * call `hf_vcpu_run` on the vCPU at a later point.
	 */
	HF_VCPU_RUN_YIELD = 1,

	/**
	 * The vCPU is blocked waiting for an interrupt. The scheduler MUST take
	 * it off the run queue and not call `hf_vcpu_run` on the vCPU until it
	 * has injected an interrupt, received `HF_VCPU_RUN_WAKE_UP` for it
	 * from another vCPU or the timeout provided in
	 * `hf_vcpu_run_return.sleep` is not `HF_SLEEP_INDEFINITE` and the
	 * specified duration has expired.
	 */
	HF_VCPU_RUN_WAIT_FOR_INTERRUPT = 2,

	/**
	 * The vCPU is blocked waiting for a message. The scheduler MUST take it
	 * off the run queue and not call `hf_vcpu_run` on the vCPU until it has
	 * injected an interrupt, sent it a message, or received
	 * `HF_VCPU_RUN_WAKE_UP` for it from another vCPU from another vCPU or
	 * the timeout provided in `hf_vcpu_run_return.sleep` is not
	 * `HF_SLEEP_INDEFINITE` and the specified duration has expired.
	 */
	HF_VCPU_RUN_WAIT_FOR_MESSAGE = 3,

	/**
	 * Hafnium would like `hf_vcpu_run` to be called on another vCPU,
	 * specified by `hf_vcpu_run_return.wake_up`. The scheduler MUST either
	 * wake the vCPU in question up if it is blocked, or preempt and re-run
	 * it if it is already running somewhere. This gives Hafnium a chance to
	 * update any CPU state which might have changed.
	 */
	HF_VCPU_RUN_WAKE_UP = 4,

	/**
	 * A message has been sent by the vCPU. The scheduler MUST run a vCPU
	 * from the recipient VM and priority SHOULD be given to those vCPUs
	 * that are waiting for a message.
	 */
	HF_VCPU_RUN_MESSAGE = 5,

	/**
	 * The vCPU has made the mailbox writable and there are pending waiters.
	 * The scheduler MUST call hf_mailbox_waiter_get() repeatedly and notify
	 * all waiters by injecting an HF_MAILBOX_WRITABLE_INTID interrupt.
	 */
	HF_VCPU_RUN_NOTIFY_WAITERS = 6,

	/**
	 * The vCPU has aborted triggering the whole VM to abort. The scheduler
	 * MUST treat this as `HF_VCPU_RUN_WAIT_FOR_INTERRUPT` for this vCPU and
	 * `HF_VCPU_RUN_WAKE_UP` for all the other vCPUs of the VM.
	 */
	HF_VCPU_RUN_ABORTED = 7,
};

struct hf_vcpu_run_return {
	enum hf_vcpu_run_code code;
	union {
		struct {
			uint32_t vm_id;
			uint16_t vcpu;
		} wake_up;
		struct {
			uint16_t vm_id;
			uint32_t size;
		} message;
		struct {
			uint64_t ns;
		} sleep;
	};
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
		ret |= (uint64_t)res.message.vm_id << 16;
		break;
	case HF_VCPU_RUN_WAIT_FOR_INTERRUPT:
	case HF_VCPU_RUN_WAIT_FOR_MESSAGE:
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
		ret.message.vm_id = (res >> 16) & 0xffff;
		break;
	case HF_VCPU_RUN_WAIT_FOR_INTERRUPT:
	case HF_VCPU_RUN_WAIT_FOR_MESSAGE:
		ret.sleep.ns = res >> 8;
		break;
	default:
		break;
	}

	return ret;
}
