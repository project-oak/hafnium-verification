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
use crate::addr::*;
use crate::arch::*;
use crate::cpu::*;
use crate::list::*;
use crate::mm::*;
use crate::mpool::*;
use crate::page::*;
use crate::spci::*;
use crate::spinlock::*;
use crate::std::*;
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

/// Prepares the vcpu to run by updating its state and fetching whether a return
/// value needs to be forced onto the vCPU.
unsafe fn api_vcpu_prepare_run(
    current: *const VCpu,
    vcpu: *mut VCpu,
    run_ret: *mut HfVCpuRunReturn,
) -> bool {
    let mut need_vm_lock;
    let ret;

    // Wait until the registers become available. All locks must be released
    // between iterations of this loop to avoid potential deadlocks if, on
    // any path, a lock needs to be taken after taking the decision to
    // switch context but before the registers have been saved.
    //
    // The VM lock is not needed in the common case so it must only be taken
    // when it is going to be needed. This ensures there are no inter-vCPU
    // dependencies in the common run case meaning the sensitive context
    // switch performance is consistent.
    loop {
        sl_lock(&(*vcpu).lock);

        // The VM needs to be locked to deliver mailbox messages.
        need_vm_lock = (*vcpu).state == VCpuStatus::BlockedMailbox;
        if need_vm_lock {
            sl_unlock(&(*vcpu).lock);
            sl_lock(&(*(*vcpu).vm).lock);
            sl_lock(&(*vcpu).lock);
        }

        if (*vcpu).regs_available {
            break;
        }

        if (*vcpu).state == VCpuStatus::Running {
            // vCPU is running on another pCPU.
            //
            // It's ok not to return the sleep duration here because
            // the other physical CPU that is currently running this
            // vCPU will return the sleep duration if needed. The
            // default return value is
            // HF_VCPU_RUN_WAIT_FOR_INTERRUPT, so no need to set it
            // explicitly.
            ret = false;
            // goto out;
            sl_unlock(&(*vcpu).lock);
            if need_vm_lock {
                sl_unlock(&(*(*vcpu).vm).lock);
            }

            return ret;
        }

        sl_unlock(&(*vcpu).lock);
        if need_vm_lock {
            sl_unlock(&(*(*vcpu).vm).lock);
        }

        if (*(*vcpu).vm).aborting.load(Ordering::Relaxed) {
            if (*vcpu).state != VCpuStatus::Aborted {
                dlog!(
                    "Aborting VM {} vCPU {}\n",
                    (*(*vcpu).vm).id,
                    vcpu_index(vcpu)
                );
                (*vcpu).state = VCpuStatus::Aborted;
            }
            ret = false;
            // goto out;
            sl_unlock(&(*vcpu).lock);
            if need_vm_lock {
                sl_unlock(&(*(*vcpu).vm).lock);
            }

            return ret;
        }

        match (*vcpu).state {
            VCpuStatus::Running | VCpuStatus::Off | VCpuStatus::Aborted => {
                ret = false;
                // goto out;
                sl_unlock(&(*vcpu).lock);
                if need_vm_lock {
                    sl_unlock(&(*(*vcpu).vm).lock);
                }

                return ret;
            }

            VCpuStatus::BlockedMailbox
                // A pending message allows the vCPU to run so the message can
                // be delivered directly.
                if (*(*vcpu).vm).mailbox.state == MailboxState::Received => {
                    arch_regs_set_retval(&mut (*vcpu).regs, SPCI_SUCCESS as uintreg_t);
                    (*(*vcpu).vm).mailbox.state = MailboxState::Read;
                    // break;
                }
                // Fall through. (TODO: isn't it too verbose?)

            VCpuStatus::BlockedMailbox | VCpuStatus::BlockedInterrupt
                // Allow virtual interrupts to be delivered.
                if (*vcpu).interrupts.enabled_and_pending_count > 0 => {
                    // break;
                }

            VCpuStatus::BlockedMailbox | VCpuStatus::BlockedInterrupt
                // The timer expired so allow the interrupt to be delivered.
                if arch_timer_pending(&(*vcpu).regs) => {
                    // break;
                }

            VCpuStatus::BlockedMailbox | VCpuStatus::BlockedInterrupt => {
                // The vCPU is not ready to run, return the appropriate code to
                // the primary which called vcpu_run.
                if arch_timer_enabled(&(*vcpu).regs) {
                    (*run_ret).code =
                        if (*vcpu).state == VCpuStatus::BlockedMailbox {
                            HfVCpuRunCode::WaitForMessage
                        } else {
                            HfVCpuRunCode::WaitForInterrupt
                        };
                    (*run_ret).detail.sleep = HfVCpuRunSleep {
                        ns: arch_timer_remaining_ns(&mut (*vcpu).regs),
                    };
                }

                ret = false;
                // goto out;
                sl_unlock(&(*vcpu).lock);
                if need_vm_lock {
                    sl_unlock(&(*(*vcpu).vm).lock);
                }

                return ret;
            }

            VCpuStatus::BlockedMailbox | VCpuStatus::Ready => {
                // break;
            }

        }

        // It has been decided that the vCPU should be run.
        (*vcpu).cpu = (*current).cpu;
        (*vcpu).state = VCpuStatus::Running;
    }

    // Mark the registers as unavailable now that we're about to reflect
    // them onto the real registers. This will also prevent another physical
    // CPU from trying to read these registers.
    (*vcpu).regs_available = false;

    ret = true;

    // out:
    sl_unlock(&(*vcpu).lock);
    if need_vm_lock {
        sl_unlock(&(*(*vcpu).vm).lock);
    }

    return ret;
}

/// Runs the given vcpu of the given vm.
#[no_mangle]
pub unsafe extern "C" fn api_vcpu_run(
    vm_id: spci_vm_id_t,
    vcpu_idx: spci_vcpu_index_t,
    current: *const VCpu,
    next: *mut *mut VCpu,
) -> HfVCpuRunReturn {
    let vm;
    let vcpu;
    let mut ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::WaitForInterrupt,
        detail: HfVCpuRunDetail {
            sleep: HfVCpuRunSleep {
                ns: HF_SLEEP_INDEFINITE,
            },
        },
    };

    // Only the primary VM can switch vcpus.
    if (*(*current).vm).id != HF_PRIMARY_VM_ID {
        return ret;
    }

    // Only the secondary VM vcpus can be run.
    if vm_id == HF_PRIMARY_VM_ID {
        return ret;
    }

    // The requested VM must exist.
    vm = vm_find(vm_id);
    if vm == ptr::null_mut() {
        return ret;
    }

    // The requested vcpu must exist.
    if vcpu_idx >= (*vm).vcpu_count {
        return ret;
    }

    // Update state if allowed.
    vcpu = vm_get_vcpu(vm, vcpu_idx);
    if !api_vcpu_prepare_run(current, vcpu, &mut ret) {
        return ret;
    }

    // Inject timer interrupt if timer has expired. It's safe to access
    // vcpu->regs here because api_vcpu_prepare_run already made sure that
    // regs_available was true (and then set it to false) before returning
    // true.
    if arch_timer_pending(&mut (*vcpu).regs) {
        // Make virtual timer interrupt pending.
        internal_interrupt_inject(vcpu, HF_VIRTUAL_TIMER_INTID, vcpu, ptr::null_mut());

        // Set the mask bit so the hardware interrupt doesn't fire
        // again. Ideally we wouldn't do this because it affects what
        // the secondary vcPU sees, but if we don't then we end up with
        // a loop of the interrupt firing each time we try to return to
        // the secondary vCPU.
        arch_timer_mask(&mut (*vcpu).regs);
    }

    // Switch to the vcpu.
    *next = vcpu;

    // Set a placeholder return code to the scheduler. This will be
    // overwritten when the switch back to the primary occurs.
    ret.code = HfVCpuRunCode::Preempted;

    return ret;
}

/// Check that the mode indicates memory that is vaid, owned and exclusive.
fn api_mode_valid_owned_and_exclusive(mode: c_int) -> bool {
    (mode as u32 & (Mode::INVALID | Mode::UNOWNED | Mode::SHARED).bits()) == 0
}

/// Determines the value to be returned by api_vm_configure and
/// api_mailbox_clear after they've succeeded. If a secondary VM is running and
/// there are waiters, it also switches back to the primary VM for it to wake
/// waiters up.
unsafe fn api_waiter_result(locked_vm: VmLocked, current: *mut VCpu, next: *mut *mut VCpu) -> i64 {
    let vm = locked_vm.vm;
    let ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::NotifyWaiters,
        detail: mem::uninitialized(),
    };

    if list_empty(&(*vm).mailbox.waiter_list) {
        // No waiters, nothing else to do.
        return 0;
    }

    if (*vm).id == HF_PRIMARY_VM_ID {
        // The caller is the primary VM. Tell it to wake up waiters.
        return 1;
    }

    // Switch back to the primary VM, informing it that there are waiters
    // that need to be notified.
    *next = api_switch_to_primary(current, ret, VCpuStatus::Ready);

    0
}

/// Configures the hypervisor's stage-1 view of the send and receive pages. The
/// stage-1 page tables must be locked so memory cannot be taken by another core
/// which could result in this transaction being unable to roll back in the case
/// of an error.
unsafe fn api_vm_configure_stage1(
    vm_locked: VmLocked,
    pa_send_begin: paddr_t,
    pa_send_end: paddr_t,
    pa_recv_begin: paddr_t,
    pa_recv_end: paddr_t,
    local_page_pool: *mut MPool,
) -> bool {
    let ret;
    let mut mm_stage1_locked = mm_lock_stage1();

    // Map the send page as read-only in the hypervisor address space.
    (*vm_locked.vm).mailbox.send = mm_identity_map(
        mm_stage1_locked,
        pa_send_begin,
        pa_send_end,
        Mode::R.bits() as i32,
        local_page_pool,
    ) as usize as *const SpciMessage;
    if (*vm_locked.vm).mailbox.send == ptr::null() {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        mm_defrag(mm_stage1_locked, local_page_pool);

        // goto fail;
        ret = false;

        mm_unlock_stage1(&mut mm_stage1_locked);
        return ret;
    }

    // Map the receive page as writable in the hypervisor address space. On
    // failure, unmap the send page before returning.
    (*vm_locked.vm).mailbox.recv = mm_identity_map(
        mm_stage1_locked,
        pa_recv_begin,
        pa_recv_end,
        Mode::W.bits() as i32,
        local_page_pool,
    ) as usize as *mut SpciMessage;
    if (*vm_locked.vm).mailbox.recv == ptr::null_mut() {
        // TODO: parital defrag of failed range.
        // Recover any memory consumed in failed mapping.
        mm_defrag(mm_stage1_locked, local_page_pool);

        // goto fail_undo_send;
        (*vm_locked.vm).mailbox.send = ptr::null();
        assert!(mm_unmap(
            mm_stage1_locked,
            pa_send_begin,
            pa_send_end,
            local_page_pool
        ));

        ret = false;

        mm_unlock_stage1(&mut mm_stage1_locked);
        return ret;
    }

    ret = true;
    // goto out;
    mm_unlock_stage1(&mut mm_stage1_locked);
    return ret;

    // The following mappings will not require more memory than is available
    // in the local pool.
    // fail_undo_send:
    (*vm_locked.vm).mailbox.send = ptr::null();
    assert!(mm_unmap(
        mm_stage1_locked,
        pa_send_begin,
        pa_send_end,
        local_page_pool
    ));

    // fail:
    ret = false;

    // out:
    mm_unlock_stage1(&mut mm_stage1_locked);
    return ret;
}

/// Configures the send and receive pages in the VM stage-2 and hypervisor
/// stage-1 page tables. Locking of the page tables combined with a local memory
/// pool ensures there will always be enough memory to recover from any errors
/// that arise.
unsafe fn api_vm_configure_pages(
    vm_locked: VmLocked,
    pa_send_begin: paddr_t,
    pa_send_end: paddr_t,
    orig_send_mode: c_int,
    pa_recv_begin: paddr_t,
    pa_recv_end: paddr_t,
    orig_recv_mode: c_int,
) -> bool {
    let ret;
    let mut local_page_pool: MPool = mem::uninitialized();

    // Create a local pool so any freed memory can't be used by another
    // thread. This is to ensure the original mapping can be restored if any
    // stage of the process fails.
    mpool_init_with_fallback(&mut local_page_pool, API_PAGE_POOL.get_ref());

    // Take memory ownership away from the VM and mark as shared.
    if !mm_vm_identity_map(
        &mut (*vm_locked.vm).ptable,
        pa_send_begin,
        pa_send_end,
        (Mode::UNOWNED | Mode::SHARED | Mode::R | Mode::W).bits() as c_int,
        ptr::null_mut(),
        &mut local_page_pool,
    ) {
        //goto fail;
        ret = false;
        mpool_fini(&mut local_page_pool);
        return ret;
    }

    if !mm_vm_identity_map(
        &mut (*vm_locked.vm).ptable,
        pa_recv_begin,
        pa_recv_end,
        (Mode::UNOWNED | Mode::SHARED | Mode::R).bits() as c_int,
        ptr::null_mut(),
        &mut local_page_pool,
    ) {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        mm_vm_defrag(&mut (*vm_locked.vm).ptable, &mut local_page_pool);
        // goto fail_undo_send;
        assert!(mm_vm_identity_map(
            &mut (*vm_locked.vm).ptable,
            pa_send_begin,
            pa_send_end,
            orig_send_mode,
            ptr::null_mut(),
            &mut local_page_pool
        ));
        ret = false;
        mpool_fini(&mut local_page_pool);
        return ret;
    }

    if !api_vm_configure_stage1(
        vm_locked,
        pa_send_begin,
        pa_send_end,
        pa_recv_begin,
        pa_recv_end,
        &mut local_page_pool,
    ) {
        // goto fail_undo_send_and_recv;
        assert!(mm_vm_identity_map(
            &mut (*vm_locked.vm).ptable,
            pa_recv_begin,
            pa_recv_end,
            orig_recv_mode,
            ptr::null_mut(),
            &mut local_page_pool
        ));

        assert!(mm_vm_identity_map(
            &mut (*vm_locked.vm).ptable,
            pa_send_begin,
            pa_send_end,
            orig_send_mode,
            ptr::null_mut(),
            &mut local_page_pool
        ));

        ret = false;

        mpool_fini(&mut local_page_pool);
        return ret;
    }

    ret = true;
    // goto out;
    mpool_fini(&mut local_page_pool);
    return ret;

    // The following mappings will not require more memory than is available
    // in the local pool.
    // fail_undo_send_and_recv:
    assert!(mm_vm_identity_map(
        &mut (*vm_locked.vm).ptable,
        pa_recv_begin,
        pa_recv_end,
        orig_recv_mode,
        ptr::null_mut(),
        &mut local_page_pool
    ));

    // fail_undo_send:
    assert!(mm_vm_identity_map(
        &mut (*vm_locked.vm).ptable,
        pa_send_begin,
        pa_send_end,
        orig_send_mode,
        ptr::null_mut(),
        &mut local_page_pool
    ));

    // fail:
    ret = false;

    // out:
    mpool_fini(&mut local_page_pool);
    return ret;
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
pub unsafe extern "C" fn api_vm_configure(
    send: ipaddr_t,
    recv: ipaddr_t,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> i64 {
    let vm = (*current).vm;
    let ret;
    let mut orig_send_mode = mem::uninitialized();
    let mut orig_recv_mode = mem::uninitialized();

    // Fail if addresses are not page-aligned.
    if !is_aligned(ipa_addr(send), PAGE_SIZE) || !is_aligned(ipa_addr(recv), PAGE_SIZE) {
        return -1;
    }

    // Convert to physical addresses.
    let pa_send_begin = pa_from_ipa(send);
    let pa_send_end = pa_add(pa_send_begin, PAGE_SIZE);

    let pa_recv_begin = pa_from_ipa(recv);
    let pa_recv_end = pa_add(pa_recv_begin, PAGE_SIZE);

    // Fail if the same page is used for the send and receive pages.
    if pa_addr(pa_send_begin) == pa_addr(pa_recv_begin) {
        return -1;
    }

    // The hypervisor's memory map must be locked for the duration of this
    // operation to ensure there will be sufficient memory to recover from
    // any failures.
    //
    // TODO: the scope of the can be reduced but will require restructing
    //       to keep a single unlock point.
    let mut vm_locked = vm_lock(vm);

    // We only allow these to be setup once.
    if (*vm).mailbox.send != ptr::null() || (*vm).mailbox.recv != ptr::null_mut() {
        // goto fail;
        ret = -1;
        vm_unlock(&mut vm_locked);
        return ret;
    }

    // Ensure the pages are valid, owned and exclusive to the VM and that
    // the VM has the required access to the memory.
    if !mm_vm_get_mode(
        &mut (*vm).ptable,
        send,
        ipa_add(send, PAGE_SIZE),
        &mut orig_send_mode,
    ) || !api_mode_valid_owned_and_exclusive(orig_send_mode)
        || (orig_send_mode & Mode::R.bits() as c_int) == 0
        || (orig_send_mode & Mode::W.bits() as c_int) == 0
    {
        // goto fail;
        ret = -1;
        vm_unlock(&mut vm_locked);
        return ret;
    }

    if !mm_vm_get_mode(
        &mut (*vm).ptable,
        recv,
        ipa_add(recv, PAGE_SIZE),
        &mut orig_recv_mode,
    ) || !api_mode_valid_owned_and_exclusive(orig_recv_mode)
        || (orig_recv_mode & Mode::R.bits() as c_int) == 0
    {
        // goto fail;
        ret = -1;
        vm_unlock(&mut vm_locked);
        return ret;
    }

    if !api_vm_configure_pages(
        vm_locked,
        pa_send_begin,
        pa_send_end,
        orig_send_mode,
        pa_recv_begin,
        pa_recv_end,
        orig_recv_mode,
    ) {
        // goto fail;
        ret = -1;
        vm_unlock(&mut vm_locked);
        return ret;
    }

    // Tell caller about waiters, if any.
    ret = api_waiter_result(vm_locked, current, next);
    // goto exit;
    vm_unlock(&mut vm_locked);
    return ret;

    // fail:
    ret = -1;

    // exit:
    vm_unlock(&mut vm_locked);
    return ret;
}

/// Copies data from the sender's send buffer to the recipient's receive buffer
/// and notifies the recipient.
///
/// If the recipient's receive buffer is busy, it can optionally register the
/// caller to be notified when the recipient's receive buffer becomes available.
#[no_mangle]
pub unsafe extern "C" fn api_spci_msg_send(
    attributes: u32,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> spci_return_t {
    let from = (*current).vm;

    let mut primary_ret = HfVCpuRunReturn {
        code: HfVCpuRunCode::Message,
        detail: mem::uninitialized(),
    };

    // TODO: Refactor the control flow of this function, and make this variable
    // immutable.
    let mut ret;

    let notify = (attributes & SPCI_MSG_SEND_NOTIFY_MASK) == SPCI_MSG_SEND_NOTIFY;

    // Check that the sender has configured its send buffer. Copy the
    // message header. If the tx mailbox at from_msg is configured (i.e.
    // from_msg != ptr::null()) then it can be safely accessed after releasing
    // the lock since the tx mailbox address can only be configured once.
    sl_lock(&(*from).lock);
    let from_msg = (*from).mailbox.send;
    sl_unlock(&(*from).lock);

    if from_msg == ptr::null() {
        return SPCI_INVALID_PARAMETERS;
    }

    // Note that the payload is not copied when the message header is.
    let mut from_msg_replica = ptr::read(from_msg);

    // Ensure source VM id corresponds to the current VM.
    if from_msg_replica.source_vm_id != (*from).id {
        return SPCI_INVALID_PARAMETERS;
    }

    let size = from_msg_replica.length as usize;
    // Limit the size of transfer.
    if size > SPCI_MSG_PAYLOAD_MAX {
        return SPCI_INVALID_PARAMETERS;
    }

    // Disallow reflexive requests as this suggests an error in the VM.
    if from_msg_replica.target_vm_id == (*from).id {
        return SPCI_INVALID_PARAMETERS;
    }

    // Ensure the target VM exists.
    let to = vm_find(from_msg_replica.target_vm_id);
    if to == ptr::null_mut() {
        return SPCI_INVALID_PARAMETERS;
    }

    // Hf needs to hold the lock on `to` before the mailbox state is
    // checked. The lock on `to` must be held until the information is
    // copied to `to` Rx buffer. Since in
    // spci_msg_handle_architected_message we may call api_spci_share_memory
    // which must hold the `from` lock, we must hold the `from` lock at this
    // point to prevent a deadlock scenario.
    let mut vm_from_to_lock = vm_lock_both(to, from);

    if (*to).mailbox.state != MailboxState::Empty || (*to).mailbox.recv == ptr::null_mut() {
        // Fail if the target isn't currently ready to receive data,
        // setting up for notification if requested.
        if notify {
            let entry = &mut (*(*current).vm).wait_entries[from_msg_replica.target_vm_id as usize];

            // Append waiter only if it's not there yet.
            if list_empty(&(*entry).wait_links) {
                list_append(&mut (*to).mailbox.waiter_list, &mut (*entry).wait_links);
            }
        }

        ret = SPCI_BUSY;
        // goto out;
        vm_unlock(&mut vm_from_to_lock.vm1);
        vm_unlock(&mut vm_from_to_lock.vm2);

        return ret;
    }

    let to_msg = (*to).mailbox.recv;

    // Handle architected messages.
    if from_msg_replica.flags & SPCI_MESSAGE_IMPDEF_MASK != SPCI_MESSAGE_IMPDEF {
        // Buffer holding the internal copy of the shared memory regions.
        // TODO: Buffer is temporarily in the stack.
        let mut message_buffer: [u8; mem::size_of::<SpciArchitectedMessageHeader>()
            + mem::size_of::<SpciMemoryRegionConstituent>()
            + mem::size_of::<SpciMemoryRegion>()] = mem::uninitialized();

        let architected_header = spci_get_architected_message_header((*from).mailbox.send);

        if from_msg_replica.length as usize > message_buffer.len() {
            ret = SPCI_INVALID_PARAMETERS;
            // goto out;
            vm_unlock(&mut vm_from_to_lock.vm1);
            vm_unlock(&mut vm_from_to_lock.vm2);

            return ret;
        }

        if (from_msg_replica.length as usize) < mem::size_of::<SpciArchitectedMessageHeader>() {
            ret = SPCI_INVALID_PARAMETERS;
            // goto out;
            vm_unlock(&mut vm_from_to_lock.vm1);
            vm_unlock(&mut vm_from_to_lock.vm2);

            return ret;
        }

        // Copy the architected message into an internal buffer.
        memcpy_s(
            message_buffer.as_mut_ptr() as _,
            message_buffer.len(),
            architected_header as _,
            from_msg_replica.length as usize,
        );

        let architected_message_replica: *mut SpciArchitectedMessageHeader =
            message_buffer.as_mut_ptr() as usize as *mut _;

        // Note that message_buffer is passed as the third parameter to
        // spci_msg_handle_architected_message. The execution flow
        // commencing at spci_msg_handle_architected_message will make
        // several accesses to fields in message_buffer. The memory area
        // message_buffer must be exclusively owned by Hf so that TOCTOU
        // issues do not arise.
        ret = spci_msg_handle_architected_message(
            vm_from_to_lock.vm1,
            vm_from_to_lock.vm2,
            architected_message_replica,
            &mut from_msg_replica,
            to_msg,
        );

        if ret != SPCI_SUCCESS {
            //goto out;
            vm_unlock(&mut vm_from_to_lock.vm1);
            vm_unlock(&mut vm_from_to_lock.vm2);

            return ret;
        }
    } else {
        // Copy data.
        memcpy_s(
            &mut (*to_msg).payload as *mut _ as usize as _,
            SPCI_MSG_PAYLOAD_MAX,
            &(*(*from).mailbox.send).payload as *const _ as usize as _,
            size,
        );
        *to_msg = from_msg_replica;
    }

    primary_ret.detail.message.vm_id = (*to).id;
    ret = SPCI_SUCCESS;

    // Messages for the primary VM are delivered directly.
    if (*to).id == HF_PRIMARY_VM_ID {
        (*to).mailbox.state = MailboxState::Read;
        *next = api_switch_to_primary(current, primary_ret, VCpuStatus::Ready);

        // goto out;
        vm_unlock(&mut vm_from_to_lock.vm1);
        vm_unlock(&mut vm_from_to_lock.vm2);

        return ret;
    }

    (*to).mailbox.state = MailboxState::Received;

    // Return to the primary VM directly or with a switch.
    if (*from).id != HF_PRIMARY_VM_ID {
        *next = api_switch_to_primary(current, primary_ret, VCpuStatus::Ready);
    }

    // out:
    vm_unlock(&mut vm_from_to_lock.vm1);
    vm_unlock(&mut vm_from_to_lock.vm2);

    return ret;
}
