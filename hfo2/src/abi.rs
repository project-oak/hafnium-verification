/*
 * Copyright 2019 Sanguk Park
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

use crate::types::*;

#[repr(C)]
#[derive(Copy, Clone)]
pub enum HfVCpuRunCode {
    /// The vCPU has been preempted but still has work to do. If the scheduling
    /// quantum has not expired, the scheduler MUST call `hf_vcpu_run` on the
    /// vCPU to allow it to continue.
    Preempted = 0,

    /// The vCPU has voluntarily yielded the CPU. The scheduler SHOULD take a
    /// scheduling decision to give cycles to those that need them but MUST
    /// call `hf_vcpu_run` on the vCPU at a later point.
    Yield = 1,

    /// The vCPU is blocked waiting for an interrupt. The scheduler MUST take
    /// it off the run queue and not call `hf_vcpu_run` on the vCPU until it
    /// has injected an interrupt, received `HF_VCPU_RUN_WAKE_UP` for it from
    /// another vCPU or the timeout provided in `hf_vcpu_run_return.sleep` is
    /// not `HF_SLEEP_INDEFINITE` and the specified duration has expired.
    WaitForInterrupt = 2,

    /// The vCPU is blocked waiting for a message. The scheduler MUST take it
    /// off the run queue and not call `hf_vcpu_run` on the vCPU until it has
    /// injected an interrupt, sent it a message, or received
    /// `HF_VCPU_RUN_WAKE_UP` for it from another vCPU from another vCPU or
    /// the timeout provided in `hf_vcpu_run_return.sleep` is not
    /// `HF_SLEEP_INDEFINITE` and the specified duration has expired.
    WaitForMessage = 3,

    /// Hafnium would like `hf_vcpu_run` to be called on another vCPU,
    /// specified by `hf_vcpu_run_return.wake_up`. The scheduler MUST either
    /// wake the vCPU in question up if it is blocked, or preempt and re-run
    /// it if it is already running somewhere. This gives Hafnium a chance to
    /// update any CPU state which might have changed.
    WakeUp = 4,

    /// A message has been sent by the vCPU. The scheduler MUST run a vCPU from
    /// the recipient VM and priority SHOULD be given to those vCPUs that are
    /// waiting for a message.
    Message = 5,

    /// The vCPU has made the mailbox writable and there are pending waiters.
    /// The scheduler MUST call hf_mailbox_waiter_get() repeatedly and notify
    /// all waiters by injecting an HF_MAILBOX_WRITABLE_INTID interrupt.
    NotifyWaiters = 6,

    /// The vCPU has aborted triggering the whole VM to abort. The scheduler
    /// MUST treat this as `HF_VCPU_RUN_WAIT_FOR_INTERRUPT` for this vCPU and
    /// `HF_VCPU_RUN_WAKE_UP` for all the other vCPUs of the VM.
    Aborted = 7,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct HfVCpuRunWakeUp {
    pub vm_id: spci_vm_id_t,
    pub vcpu: spci_vcpu_index_t,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct HfVCpuRunMessage {
    pub vm_id: spci_vm_id_t,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct HfVCpuRunSleep {
    pub ns: u64,
}

#[repr(C)]
pub union HfVCpuRunDetail {
    pub wake_up: HfVCpuRunWakeUp,
    pub message: HfVCpuRunMessage,
    pub sleep: HfVCpuRunSleep,
}

#[repr(C)]
pub struct HfVCpuRunReturn {
    pub code: HfVCpuRunCode,
    pub detail: HfVCpuRunDetail,
}

#[repr(C)]
#[derive(PartialEq)]
pub enum HfShare {
    /// Relinquish ownership and access to the memory and pass them to the
    /// recipient.
    Give,

    /// Retain ownership of the memory but relinquish access to the recipient.
    Lend,

    /// Retain ownership and access but additionally allow access to the
    /// recipient.
    Share,
}

/// Encode an HfVCpuRunReturn struct in the 64-bit packing ABI.
#[inline]
pub unsafe fn hf_vcpu_run_return_encode(res: HfVCpuRunReturn) -> u64 {
    let mut ret = res.code as u64 & 0xff;

    match res.code {
        HfVCpuRunCode::WakeUp => {
            ret |= (res.detail.wake_up.vm_id as u64) << 32;
            ret |= (res.detail.wake_up.vcpu as u64) << 16;
        }
        HfVCpuRunCode::Message => {
            ret |= (res.detail.message.vm_id as u64) << 8;
        }
        HfVCpuRunCode::WaitForInterrupt | HfVCpuRunCode::WaitForMessage => {
            ret |= (res.detail.sleep.ns as u64) << 8;
        }
        _ => (),
    }

    ret
}
