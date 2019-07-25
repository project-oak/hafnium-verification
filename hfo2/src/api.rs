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

use core::mem::{self, MaybeUninit};
use core::ptr;
use core::sync::atomic::Ordering;

use crate::abi::*;
use crate::arch::*;
use crate::cpu::*;
use crate::list::*;
use crate::mpool::*;
use crate::page::*;
use crate::spci::*;
use crate::spinlock::*;
use crate::types::*;
use crate::vm::*;

// To eliminate the risk of deadlocks, we define a partial order for the acquisition of locks held
// concurrently by the same physical CPU. Our current ordering requirements are as follows:
//
// vm::lock -> vcpu::lock -> mm_stage1_lock -> dlog sl
//
// Locks of the same kind require the lock of lowest address to be locked first, see
// `sl_lock_both()`.

// Currently, a page is mapped for the send and receive buffers so the maximum request is the size
// of a page.
const_assert_eq!(hf_mailbox_size; HF_MAILBOX_SIZE, PAGE_SIZE);

static mut API_PAGE_POOL: MaybeUninit<MPool> = MaybeUninit::uninit();

/// Initialises the API page pool by taking ownership of the contents of the
/// given page pool.
#[no_mangle]
pub unsafe extern "C" fn api_init(ppool: *mut MPool) {
    mpool_init_from(API_PAGE_POOL.get_mut(), ppool);
}

/// Switches the physical CPU back to the corresponding vcpu of the primary VM.
///
/// This triggers the scheduling logic to run. Run in the context of secondary
/// VM to cause HF_VCPU_RUN to return and the primary VM to regain control of
/// the cpu.
#[no_mangle]
pub unsafe extern "C" fn api_switch_to_primary(
    current: *mut VCpu,
    mut primary_ret: HfVCpuRunReturn,
    secondary_state: VCpuStatus,
) -> *mut VCpu {
    let primary = vm_find(HF_PRIMARY_VM_ID);
    let next = vm_get_vcpu(primary, cpu_index((*current).cpu) as spci_vcpu_index_t);

    // If the secondary is blocked but has a timer running, sleep until the
    // timer fires rather than indefinitely.
    match primary_ret.code {
        HfVCpuRunCode::WaitForInterrupt | HfVCpuRunCode::WaitForMessage => {
            primary_ret.detail.sleep.ns = if arch_timer_enabled_current() {
                arch_timer_remaining_ns_current()
            } else {
                HF_SLEEP_INDEFINITE
            };
        }

        _ =>
        /* Do nothing */
        {
            ()
        }
    }

    // Set the return value for the primary VM's call to HF_VCPU_RUN.
    arch_regs_set_retval(&mut (*next).regs, hf_vcpu_run_return_encode(primary_ret));

    // Mark the current vcpu as waiting.
    sl_lock(&(*current).lock);
    (*current).state = secondary_state;
    sl_unlock(&(*current).lock);

    next
}

/// Returns to the primary vm and signals that the vcpu still has work to do so.
#[no_mangle]
pub unsafe extern "C" fn api_preempt(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::Preempted,
        detail: mem::uninitialized(),
    };

    api_switch_to_primary(current, ret, VCpuStatus::Ready)
}

/// Puts the current vcpu in wait for interrupt mode, and returns to the primary
/// vm.
#[no_mangle]
pub unsafe extern "C" fn api_wait_for_interrupt(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::WaitForInterrupt,
        detail: mem::uninitialized(),
    };

    api_switch_to_primary(current, ret, VCpuStatus::BlockedInterrupt)
}

/// Puts the current vCPU in off mode, and returns to the primary VM.
#[no_mangle]
pub unsafe extern "C" fn api_vcpu_off(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::WaitForInterrupt,
        detail: mem::uninitialized(),
    };

    // Disable the timer, so the scheduler doesn't get told to call back
    // based on it.
    arch_timer_disable_current();

    api_switch_to_primary(current, ret, VCpuStatus::Off)
}

/// Returns to the primary vm to allow this cpu to be used for other tasks as
/// the vcpu does not have work to do at this moment. The current vcpu is masked
/// as ready to be scheduled again. This SPCI function always returns
/// SPCI_SUCCESS.
#[no_mangle]
pub unsafe extern "C" fn api_spci_yield(current: *mut VCpu, next: *mut *mut VCpu) -> i32 {
    let ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::Yield,
        detail: mem::uninitialized(),
    };

    if (*(*current).vm).id == HF_PRIMARY_VM_ID {
        // Noop on the primary as it makes the scheduling decisions.
        return SPCI_SUCCESS;
    }

    *next = api_switch_to_primary(current, ret, VCpuStatus::Ready);

    // SPCI_YIELD always returns SPCI_SUCCESS.
    SPCI_SUCCESS
}

/// Switches to the primary so that it can switch to the target, or kick tit if
/// it is already running on a different physical CPU.
#[no_mangle]
pub unsafe extern "C" fn api_wake_up(current: *mut VCpu, target_vcpu: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::WakeUp,
        detail: HfVCpuRunDetail {
            wake_up: HfVCpuRunWakeUp {
                vm_id: (*(*target_vcpu).vm).id,
                vcpu: vcpu_index(target_vcpu),
            },
        },
    };

    api_switch_to_primary(current, ret, VCpuStatus::Ready)
}

/// Aborts the vCPU and triggers its VM to abort fully.
#[no_mangle]
pub unsafe extern "C" fn api_abort(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::Aborted,
        detail: mem::uninitialized(),
    };

    dlog!(
        "Aborting VM {} vCPU {}\n",
        (*(*current).vm).id,
        vcpu_index(current)
    );

    if (*(*current).vm).id == HF_PRIMARY_VM_ID {
        // TODO: what to do when the primary aborts?
        loop {
            // Do nothing.
        }
    }

    (*(*current).vm).aborting.store(true, Ordering::Relaxed);

    // TODO: free resources once all vCPUs abort.

    api_switch_to_primary(current, ret, VCpuStatus::Aborted)
}

/// Returns the ID of the VM.
#[no_mangle]
pub unsafe extern "C" fn api_vm_get_id(current: *const VCpu) -> spci_vm_id_t {
    (*(*current).vm).id
}

/// Returns the number of VMs configured to run.
#[no_mangle]
pub unsafe extern "C" fn api_vm_get_count() -> spci_vm_count_t {
    vm_get_count()
}

/// Returns the number of vCPUs configured in the given VM, or 0 if there is no
/// such VM or the caller is not the primary VM.
#[no_mangle]
pub unsafe extern "C" fn api_vcpu_get_count(
    vm_id: spci_vm_id_t,
    current: *const VCpu,
) -> spci_vcpu_count_t {
    let vm;

    // Only the primary VM needs to know about vcpus for scheduling.
    if (*(*current).vm).id != HF_PRIMARY_VM_ID {
        return 0;
    }

    vm = vm_find(vm_id);
    if vm == ptr::null_mut() {
        return 0;
    }

    (*vm).vcpu_count
}

/// This function is called by the architecture-specific context switching
/// function to indicate that register state for the given vcpu has been saved
/// and can therefore be used by other pcpus.
#[no_mangle]
pub unsafe extern "C" fn api_regs_state_saved(vcpu: *mut VCpu) {
    sl_lock(&(*vcpu).lock);
    (*vcpu).regs_available = true;
    sl_unlock(&(*vcpu).lock);
}

/// Retrieves the next waiter and removes it from the wait list if the VM's
/// mailbox is in a writable state.
#[no_mangle]
pub unsafe extern "C" fn api_fetch_waiter(locked_vm: VmLocked) -> *mut WaitEntry {
    let entry: *mut WaitEntry;
    let vm = locked_vm.vm;

    if (*vm).mailbox.state != MailboxState::Empty
        || (*vm).mailbox.recv == ptr::null_mut()
        || list_empty(&(*vm).mailbox.waiter_list)
    {
        // The mailbox is not writable or there are no waiters.
        return ptr::null_mut();
    }

    // Remove waiter from the wait list.
    entry = container_of!((*vm).mailbox.waiter_list.next, WaitEntry, wait_links);
    list_remove(&mut (*entry).wait_links);
    entry
}

/// Assuming that the arguments have already been checked by the caller, injects
/// a virtual interrupt of the given ID into the given target vCPU. This doesn't
/// cause the vCPU to actually be run immediately; it will be taken when the
/// vCPU is next run, which is up to the scheduler.
///
/// Returns:
///  - 0 on success if no further action is needed.
///  - 1 if it was called by the primary VM and the primary VM now needs to wake
///    up or kick the target vCPU.
/// TODO: this function was using `goto` originally and it is just
/// implemented as copy-paste in Rust.
unsafe fn internal_interrupt_inject(
    target_vcpu: *mut VCpu,
    intid: u32,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> i64 {
    let intid_index = intid / INTERRUPT_REGISTER_BITS as u32;
    let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS as u32);
    let mut ret: i64 = 0;

    sl_lock(&(*target_vcpu).lock);

    // We only need to change state and (maybe) trigger a virtual IRQ if it
    // is enabled and was not previously pending. Otherwise we can skip
    // everything except setting the pending bit.
    //
    // If you change this logic make sure to update the need_vm_lock logic
    // above to match.
    if (*target_vcpu).interrupts.enabled[intid_index as usize]
        & !(*target_vcpu).interrupts.pending[intid_index as usize]
        & intid_mask
        != 0
    {
        // goto out;
        // Either way, make it pending.
        (*target_vcpu).interrupts.pending[intid_index as usize] |= intid_mask;
        sl_unlock(&(*target_vcpu).lock);
        return ret;
    }

    // Increment the count.
    (*target_vcpu).interrupts.enabled_and_pending_count += 1;

    // Only need to update state if there was not already an interrupt enabled
    // and pending.
    if (*target_vcpu).interrupts.enabled_and_pending_count != 1 {
        // goto out;
        // Either way, make it pending.
        (*target_vcpu).interrupts.pending[intid_index as usize] |= intid_mask;
        sl_unlock(&(*target_vcpu).lock);
        return ret;
    }

    if (*(*current).vm).id == HF_PRIMARY_VM_ID {
        // If the call came from the primary VM, let it know that it should
        // run or kick the target vCPU.
        ret = 1;
    } else if current != target_vcpu && next != ptr::null_mut() {
        *next = api_wake_up(current, target_vcpu);
    }

    // out:
    // Either way, make it pending.
    (*target_vcpu).interrupts.pending[intid_index as usize] |= intid_mask;
    sl_unlock(&(*target_vcpu).lock);
    return ret;
}
