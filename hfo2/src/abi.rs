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

use core::convert::TryFrom;

use crate::types::*;

#[derive(Clone, Copy, PartialEq)]
pub enum HfVCpuRunReturn {
    /// The vCPU has been preempted but still has work to do. If the scheduling
    /// quantum has not expired, the scheduler MUST call `hf_vcpu_run` on the
    /// vCPU to allow it to continue.
    Preempted,

    /// The vCPU has voluntarily yielded the CPU. The scheduler SHOULD take a
    /// scheduling decision to give cycles to those that need them but MUST
    /// call `hf_vcpu_run` on the vCPU at a later point.
    Yield,

    /// The vCPU is blocked waiting for an interrupt. The scheduler MUST take
    /// it off the run queue and not call `hf_vcpu_run` on the vCPU until it
    /// has injected an interrupt, received `HfVCpuRunReturn::WakeUp` for it
    /// from another vCPU or the timeout provided in `ns` is not
    /// `HF_SLEEP_INDEFINITE` and the specified duration has expired.
    WaitForInterrupt { ns: u64 },

    /// The vCPU is blocked waiting for a message. The scheduler MUST take it
    /// off the run queue and not call `hf_vcpu_run` on the vCPU until it has
    /// injected an interrupt, sent it a message, or received
    /// `HfVCpuRunReturn::WakeUp` for it from another vCPU from another vCPU or
    /// the timeout provided in `ns` is not `HF_SLEEP_INDEFINITE` and the
    /// specified duration has expired.
    WaitForMessage { ns: u64 },

    /// Hafnium would like `hf_vcpu_run` to be called on another vCPU,
    /// specified by `HfVCpuRunReturn::WakeUp`. The scheduler MUST either wake
    /// the vCPU in question up if it is blocked, or preempt and re-run it if
    /// it is already running somewhere. This gives Hafnium a chance to update
    /// any CPU state which might have changed.
    WakeUp {
        vm_id: spci_vm_id_t,
        vcpu: spci_vcpu_index_t,
    },

    /// A message has been sent by the vCPU. The scheduler MUST run a vCPU from
    /// the recipient VM and priority SHOULD be given to those vCPUs that are
    /// waiting for a message.
    Message { vm_id: spci_vm_id_t },

    /// The vCPU has made the mailbox writable and there are pending waiters.
    /// The scheduler MUST call hf_mailbox_waiter_get() repeatedly and notify
    /// all waiters by injecting an HF_MAILBOX_WRITABLE_INTID interrupt.
    NotifyWaiters,

    /// The vCPU has aborted triggering the whole VM to abort. The scheduler
    /// MUST treat this as `HfVCpuRunReturn::WaitForInterrupt` for this vCPU and
    /// `HfVCpuRunReturn::WakeUp` for all the other vCPUs of the VM.
    Aborted,
}

#[derive(Clone, Copy, PartialEq)]
pub enum HfShare {
    /// Relinquish ownership and access to the memory and pass them to the
    /// recipient.
    Give = 0,

    /// Retain ownership of the memory but relinquish access to the recipient.
    Lend = 1,

    /// Retain ownership and access but additionally allow access to the
    /// recipient.
    Share = 2,
}

impl HfVCpuRunReturn {
    /// Encode an HfVCpuRunReturn struct in the 64-bit packing ABI.
    pub fn into_raw(self) -> u64 {
        use HfVCpuRunReturn::*;

        match self {
            Preempted => 0,
            Yield => 1,
            WaitForInterrupt { ns } => 2 | (ns << 8),
            WaitForMessage { ns } => 3 | (ns << 8),
            WakeUp { vm_id, vcpu } => 4 | (u64::from(vm_id) << 32) | (u64::from(vcpu) << 16),
            Message { vm_id } => 5 | (u64::from(vm_id) << 8),
            NotifyWaiters => 6,
            Aborted => 7,
        }
    }
}

impl TryFrom<usize> for HfShare {
    type Error = ();

    fn try_from(from: usize) -> Result<Self, Self::Error> {
        match from {
            0 => Ok(Self::Give),
            1 => Ok(Self::Lend),
            2 => Ok(Self::Share),
            _ => Err(()),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    /// Encode a preempted response without leaking.
    #[test]
    fn abi_hf_vcpu_run_return_encode_preemptd() {
        let res = HfVCpuRunReturn::Preempted;
        assert_eq!(res.into_raw(), 0);
    }

    /// Encode a yield response without leaking.
    #[test]
    fn abi_hf_vcpu_run_return_encode_yield() {
        let res = HfVCpuRunReturn::Yield;
        assert_eq!(res.into_raw(), 1);
    }

    /// Encode wait-for-interrupt response without leaking.
    #[test]
    fn abi_hf_vcpu_run_return_encode_wait_for_interrupt() {
        let res = HfVCpuRunReturn::WaitForInterrupt {
            ns: HF_SLEEP_INDEFINITE,
        };
        assert_eq!(res.into_raw(), 0xffffffffffffff02);
    }

    /// Encoding wait-for-interrupt response with too large sleep duration will
    /// drop the top octet.
    #[test]
    fn abi_hf_vcpu_run_return_encode_wait_for_interrupt_sleep_too_long() {
        let res = HfVCpuRunReturn::WaitForInterrupt {
            ns: 0xcc22888888888888,
        };
        assert_eq!(res.into_raw(), 0x2288888888888802);
    }

    /// Encode wait-for-message response without leaking.
    #[test]
    fn abi_hf_vcpu_run_return_encode_wait_for_message() {
        let res = HfVCpuRunReturn::WaitForMessage {
            ns: HF_SLEEP_INDEFINITE,
        };
        assert_eq!(res.into_raw(), 0xffffffffffffff03);
    }

    /// Encoding wait-for-message response with too large sleep duration will
    /// drop the top octet.
    #[test]
    fn abi_hf_vcpu_run_return_encode_wait_for_message_sleep_too_long() {
        let res = HfVCpuRunReturn::WaitForMessage {
            ns: 0xaa99777777777777,
        };
        assert_eq!(res.into_raw(), 0x9977777777777703);
    }

    /// Encode wake up response without leaking.
    #[test]
    fn abi_hf_vcpu_run_return_encode_wake_up() {
        let res = HfVCpuRunReturn::WakeUp {
            vm_id: 0x1234,
            vcpu: 0xabcd,
        };
        assert_eq!(res.into_raw(), 0x1234abcd0004);
    }

    /// Encode a 'notify waiters' response without leaking.
    #[test]
    fn abi_hf_vcpu_run_return_encode_notify_waiters() {
        let res = HfVCpuRunReturn::NotifyWaiters;
        assert_eq!(res.into_raw(), 6);
    }

    /// Encode an aborted response without leaking.
    #[test]
    fn abi_hf_vcpu_run_return_encode_aborted() {
        let res = HfVCpuRunReturn::Aborted;
        assert_eq!(res.into_raw(), 7);
    }
}
