/*
 * Copyright 2019 Jeehoon Kang
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
use core::mem::ManuallyDrop;

use crate::abi::*;
use crate::addr::*;
use crate::cpu::*;
use crate::init::*;
use crate::page::*;
use crate::spci::*;
use crate::types::*;

// To eliminate the risk of deadlocks, we define a partial order for the acquisition of locks held
// concurrently by the same physical CPU. Our current ordering requirements are as follows:
//
// vcpu::execution_lock -> vm::lock -> vcpu::interrupts_lock -> mm_stage1_lock -> dlog sl
//
// Locks of the same kind require the lock of lowest address to be locked first, see
// `sl_lock_both()`.

// Currently, a page is mapped for the send and receive buffers so the maximum request is the size
// of a page.
const_assert_eq!(hf_mailbox_size; HF_MAILBOX_SIZE, PAGE_SIZE);

/// Returns to the primary vm and signals that the vcpu still has work to do so.
#[no_mangle]
pub extern "C" fn api_preempt(current: *mut VCpu) -> *const VCpu {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    hypervisor().api_preempt(&mut current)
}

/// Puts the current vcpu in wait for interrupt mode, and returns to the primary
/// vm.
#[no_mangle]
pub extern "C" fn api_wait_for_interrupt(current: *mut VCpu) -> *const VCpu {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    hypervisor().api_wait_for_interrupt(&mut current)
}

/// Puts the current vCPU in off mode, and returns to the primary VM.
#[no_mangle]
pub extern "C" fn api_vcpu_off(current: *mut VCpu) -> *const VCpu {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    hypervisor().api_vcpu_off(&mut current)
}

/// Returns to the primary vm to allow this cpu to be used for other tasks as
/// the vcpu does not have work to do at this moment. The current vcpu is masked
/// as ready to be scheduled again. This SPCI function always returns
/// SpciReturn::Success.
#[no_mangle]
pub extern "C" fn api_spci_yield(current: *mut VCpu, next: *mut *const VCpu) -> SpciReturn {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    if let Some(vcpu) = hypervisor().api_spci_yield(&mut current) {
        unsafe {
            *next = vcpu;
        }
    }

    // SPCI_YIELD always returns SPCI_SUCCESS.
    SpciReturn::Success
}

/// Switches to the primary so that it can switch to the target, or kick tit if
/// it is already running on a different physical CPU.
#[no_mangle]
pub extern "C" fn api_wake_up(current: *mut VCpu, target_vcpu: *const VCpu) -> *const VCpu {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    hypervisor().wake_up(&mut current, unsafe { &*target_vcpu })
}

/// Aborts the vCPU and triggers its VM to abort fully.
#[no_mangle]
pub extern "C" fn api_abort(current: *mut VCpu) -> *const VCpu {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    hypervisor().api_abort(&mut current)
}

/// Returns the ID of the VM.
#[no_mangle]
pub extern "C" fn api_vm_get_id(current: *const VCpu) -> spci_vm_id_t {
    hypervisor().api_vm_get_id(unsafe { &*current })
}

/// Returns the number of VMs configured to run.
#[no_mangle]
pub extern "C" fn api_vm_get_count() -> spci_vm_count_t {
    hypervisor().api_vm_get_count()
}

/// Returns the number of vCPUs configured in the given VM, or 0 if there is no
/// such VM or the caller is not the primary VM.
#[no_mangle]
pub extern "C" fn api_vcpu_get_count(
    vm_id: spci_vm_id_t,
    current: *const VCpu,
) -> spci_vcpu_count_t {
    hypervisor()
        .api_vcpu_get_count(vm_id, unsafe { &*current })
        .unwrap_or(0)
}

/// This function is called by the architecture-specific context switching
/// function to indicate that register state for the given vcpu has been saved
/// and can therefore be used by other pcpus.
#[no_mangle]
pub unsafe extern "C" fn api_regs_state_saved(vcpu: *mut VCpu) {
    if (*(*vcpu).vm).id != HF_PRIMARY_VM_ID {
        (*vcpu).inner.unlock_unchecked();
    }
}

/// Runs the given vcpu of the given vm.
#[no_mangle]
pub extern "C" fn api_vcpu_run(
    vm_id: spci_vm_id_t,
    vcpu_idx: spci_vcpu_index_t,
    current: *mut VCpu,
    next: *mut *const VCpu,
) -> u64 {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });

    match hypervisor().api_vcpu_run(vm_id, vcpu_idx, &mut current) {
        Ok(vcpu) => unsafe { *next = vcpu.into_raw() },
        Err(ret) => return ret.into_raw(),
    }

    // Set a placeholder return code to the scheduler. This will be overwritten when the switch
    // back to the primary occurs.
    HfVCpuRunReturn::Preempted.into_raw()
}

/// Configures the VM to send/receive data through the specified pages. The
/// pages must not be shared.
///
/// Returns:
///  - -1 on failure.
///  - 0 on success if no further action is needed.
///  - 1 if it was called by the primary VM and the primary VM now needs to wake
///    up or kick waiters. Waiters should be retrieved by calling
///    hf_mailbox_waiter_get.
#[no_mangle]
pub extern "C" fn api_vm_configure(
    send: ipaddr_t,
    recv: ipaddr_t,
    current: *mut VCpu,
    next: *mut *const VCpu,
) -> i64 {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    let (ret, vcpu) = hypervisor().api_vm_configure(send, recv, &mut current);

    unsafe { *next = some_or!(vcpu, return ret) };
    ret
}

/// Copies data from the sender's send buffer to the recipient's receive buffer
/// and notifies the recipient.
///
/// If the recipient's receive buffer is busy, it can optionally register the
/// caller to be notified when the recipient's receive buffer becomes available.
#[no_mangle]
pub extern "C" fn api_spci_msg_send(
    attributes: SpciMsgSendAttributes,
    current: *mut VCpu,
    next: *mut *const VCpu,
) -> SpciReturn {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    let (ret, vcpu) = hypervisor().api_spci_msg_send(attributes, &mut current);

    unsafe {
        *next = some_or!(vcpu, return ret);
    }
    ret
}

/// Receives a message from the mailbox. If one isn't available, this function
/// can optionally block the caller until one becomes available.
///
/// No new messages can be received until the mailbox has been cleared.
#[no_mangle]
pub extern "C" fn api_spci_msg_recv(
    attributes: SpciMsgRecvAttributes,
    current: *mut VCpu,
    next: *mut *const VCpu,
) -> SpciReturn {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    let (ret, vcpu) = hypervisor().api_spci_msg_recv(attributes, &mut current);

    unsafe {
        *next = some_or!(vcpu, return ret);
    }
    ret
}

/// Retrieves the next VM whose mailbox became writable. For a VM to be notified
/// by this function, the caller must have called api_mailbox_send before with
/// the notify argument set to true, and this call must have failed because the
/// mailbox was not available.
///
/// It should be called repeatedly to retrieve a list of VMs.
///
/// Returns -1 if no VM became writable, or the id of the VM whose mailbox
/// became writable.
#[no_mangle]
pub extern "C" fn api_mailbox_writable_get(current: *const VCpu) -> i64 {
    let res = some_or!(
        hypervisor().api_mailbox_writable_get(unsafe { &*current }),
        return -1
    );

    i64::from(res)
}

/// Retrieves the next VM waiting to be notified that the mailbox of the
/// specified VM became writable. Only primary VMs are allowed to call this.
///
/// Returns -1 on failure or if there are no waiters; the VM id of the next
/// waiter otherwise.
#[no_mangle]
pub extern "C" fn api_mailbox_waiter_get(vm_id: spci_vm_id_t, current: *const VCpu) -> i64 {
    let res = some_or!(
        hypervisor().api_mailbox_waiter_get(vm_id, unsafe { &*current }),
        return -1
    );

    i64::from(res)
}

/// Clears the caller's mailbox so that a new message can be received. The
/// caller must have copied out all data they wish to preserve as new messages
/// will overwrite the old and will arrive asynchronously.
///
/// Returns:
///  - -1 on failure, if the mailbox hasn't been read.
///  - 0 on success if no further action is needed.
///  - 1 if it was called by the primary VM and the primary VM now needs to wake
///    up or kick waiters. Waiters should be retrieved by calling
///    hf_mailbox_waiter_get.
#[no_mangle]
pub extern "C" fn api_mailbox_clear(current: *mut VCpu, next: *mut *const VCpu) -> i64 {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    let (ret, vcpu) = hypervisor().api_mailbox_clear(&mut current);

    unsafe {
        *next = some_or!(vcpu, return ret);
    }
    ret
}

/// Enables or disables a given interrupt ID for the calling vCPU.
///
/// Returns 0 on success, or -1 if the intid is invalid.
#[no_mangle]
pub extern "C" fn api_interrupt_enable(intid: intid_t, enable: bool, current: *const VCpu) -> i64 {
    if hypervisor()
        .api_interrupt_enable(intid, enable, unsafe { &*current })
        .is_ok()
    {
        0
    } else {
        -1
    }
}

/// Returns the ID of the next pending interrupt for the calling vCPU, and
/// acknowledges it (i.e. marks it as no longer pending). Returns
/// HF_INVALID_INTID if there are no pending interrupts.
#[no_mangle]
pub extern "C" fn api_interrupt_get(current: *const VCpu) -> intid_t {
    hypervisor().api_interrupt_get(unsafe { &*current })
}

/// Injects a virtual interrupt of the given ID into the given target vCPU.
/// This doesn't cause the vCPU to actually be run immediately; it will be taken
/// when the vCPU is next run, which is up to the scheduler.
///
/// Returns:
///  - -1 on failure because the target VM or vCPU doesn't exist, the interrupt
///    ID is invalid, or the current VM is not allowed to inject interrupts to
///    the target VM.
///  - 0 on success if no further action is needed.
///  - 1 if it was called by the primary VM and the primary VM now needs to wake
///    up or kick the target vCPU.
#[no_mangle]
pub extern "C" fn api_interrupt_inject(
    target_vm_id: spci_vm_id_t,
    target_vcpu_idx: spci_vcpu_index_t,
    intid: intid_t,
    current: *mut VCpu,
    next: *mut *const VCpu,
) -> i64 {
    let mut current = ManuallyDrop::new(unsafe { VCpuExecutionLocked::from_raw(current) });
    let (ret, vcpu) =
        hypervisor().api_interrupt_inject(target_vm_id, target_vcpu_idx, intid, &mut current);

    unsafe {
        *next = some_or!(vcpu, return ret);
    }
    ret
}

/// Shares memory from the calling VM with another. The memory can be shared in different modes.
///
/// TODO: the interface for sharing memory will need to be enhanced to allow sharing with different
///       modes e.g. read-only, informing the recipient of the memory they have been given, opting
///       to not wipe the memory and possibly allowing multiple blocks to be transferred. What this
///       will look like is TBD.
#[no_mangle]
pub extern "C" fn api_share_memory(
    vm_id: spci_vm_id_t,
    addr: ipaddr_t,
    size: size_t,
    share: usize,
    current: *const VCpu,
) -> i64 {
    // Convert the sharing request to memory management modes.
    // The input is untrusted so might not be a valid value.
    let share = ok_or!(HfShare::try_from(share), return -1);

    if hypervisor()
        .share_memory(vm_id, addr, size, share, unsafe { &*current })
        .is_ok()
    {
        0
    } else {
        -1
    }
}

/// Returns the version of the implemented SPCI specification.
#[no_mangle]
pub extern "C" fn api_spci_version() -> i32 {
    hypervisor().api_spci_version()
}

#[no_mangle]
pub extern "C" fn api_debug_log(c: c_char, current: *const VCpu) -> i64 {
    hypervisor().api_debug_log(c, unsafe { &*current });
    0
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn vm_get_count() {
        assert_eq!(hypervisor().api_vm_get_count(), 0);
    }
}
