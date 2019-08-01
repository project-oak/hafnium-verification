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
use crate::dlog::*;
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
unsafe fn api_switch_to_primary(
    current: *mut VCpu,
    mut primary_ret: HfVCpuRunReturn,
    secondary_state: VCpuStatus,
) -> *mut VCpu {
    let primary = vm_find(HF_PRIMARY_VM_ID);
    let next = vm_get_vcpu(primary, cpu_index((*current).cpu) as spci_vcpu_index_t);

    // If the secondary is blocked but has a timer running, sleep until the
    // timer fires rather than indefinitely.
    match &mut primary_ret {
        HfVCpuRunReturn::WaitForInterrupt { ns }
        | HfVCpuRunReturn::WaitForMessage { ns } => {
            *ns = if arch_timer_enabled_current() {
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
    let ret = HfVCpuRunReturn::Preempted;

    api_switch_to_primary(current, ret, VCpuStatus::Ready)
}

/// Puts the current vcpu in wait for interrupt mode, and returns to the primary
/// vm.
#[no_mangle]
pub unsafe extern "C" fn api_wait_for_interrupt(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn::WaitForInterrupt {
        // TODO: `api_switch_to_primary` always initialize this variable,
        // but it would be better if we don't use `mem::uninitialized()`.
        ns: mem::uninitialized(),
    };

    api_switch_to_primary(current, ret, VCpuStatus::BlockedInterrupt)
}

/// Puts the current vCPU in off mode, and returns to the primary VM.
#[no_mangle]
pub unsafe extern "C" fn api_vcpu_off(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn::WaitForInterrupt {
        // TODO: `api_switch_to_primary` always initialize this variable,
        // but it would be better if we don't use `mem::uninitialized()`.
        ns: mem::uninitialized(),
    };

    // Disable the timer, so the scheduler doesn't get told to call back
    // based on it.
    arch_timer_disable_current();

    api_switch_to_primary(current, ret, VCpuStatus::Off)
}

/// Returns to the primary vm to allow this cpu to be used for other tasks as
/// the vcpu does not have work to do at this moment. The current vcpu is masked
/// as ready to be scheduled again. This SPCI function always returns
/// SpciReturn::Success.
#[no_mangle]
pub unsafe extern "C" fn api_spci_yield(current: *mut VCpu, next: *mut *mut VCpu) -> SpciReturn {
    let ret = HfVCpuRunReturn::Yield;

    if (*(*current).vm).id == HF_PRIMARY_VM_ID {
        // Noop on the primary as it makes the scheduling decisions.
        return SpciReturn::Success;
    }

    *next = api_switch_to_primary(current, ret, VCpuStatus::Ready);

    // SPCI_YIELD always returns SPCI_SUCCESS.
    SpciReturn::Success
}

/// Switches to the primary so that it can switch to the target, or kick tit if
/// it is already running on a different physical CPU.
#[no_mangle]
pub unsafe extern "C" fn api_wake_up(current: *mut VCpu, target_vcpu: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn::WakeUp {
        vm_id: (*(*target_vcpu).vm).id,
        vcpu: vcpu_index(target_vcpu),
    };

    api_switch_to_primary(current, ret, VCpuStatus::Ready)
}

/// Aborts the vCPU and triggers its VM to abort fully.
#[no_mangle]
pub unsafe extern "C" fn api_abort(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn::Aborted;

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
unsafe fn api_fetch_waiter(locked_vm: VmLocked) -> *mut WaitEntry {
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
        == 0
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
/// TODO: Porting this function into Rust impacted test performance badly.
/// In order to pass all test suites,
///  - currently, enlong the time limits in test/hftest/hftest.py and
///    kokoro/ubuntu/test.sh.
///  - in the future, modify this function as one in this PR
///    (https://hafnium-review.googlesource.com/c/hafnium/+/5600).
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
            // It's ok not to return the sleep duration here because the other
            // physical CPU that is currently running this  vCPU will return
            // the sleep duration if needed. The default return value is
            // HF_VCPU_RUN_WAIT_FOR_INTERRUPT, so no need to set it explicitly.
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

        // A pending message allows the vCPU to run so the message can be
        // delivered directly.
        VCpuStatus::BlockedMailbox if (*(*vcpu).vm).mailbox.state == MailboxState::Received => {
            arch_regs_set_retval(&mut (*vcpu).regs, SpciReturn::Success as uintreg_t);
            (*(*vcpu).vm).mailbox.state = MailboxState::Read;
            // break;
        }
        // Fall through. (TODO: isn't it too verbose?)

        // Allow virtual interrupts to be delivered.
        VCpuStatus::BlockedMailbox | VCpuStatus::BlockedInterrupt
            if (*vcpu).interrupts.enabled_and_pending_count > 0 =>
        {
            // break;
        }

        // The timer expired so allow the interrupt to be delivered.
        VCpuStatus::BlockedMailbox | VCpuStatus::BlockedInterrupt
            if arch_timer_pending(&(*vcpu).regs) =>
        {
            // break;
        }

        // The vCPU is not ready to run, return the appropriate code to the
        // primary which called vcpu_run.
        VCpuStatus::BlockedMailbox | VCpuStatus::BlockedInterrupt => {
            if arch_timer_enabled(&(*vcpu).regs) {
                let ns = arch_timer_remaining_ns(&mut (*vcpu).regs);

                *run_ret = if (*vcpu).state == VCpuStatus::BlockedMailbox {
                    HfVCpuRunReturn::WaitForMessage { ns }
                } else {
                    HfVCpuRunReturn::WaitForInterrupt { ns }
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

        VCpuStatus::Ready => {
            // break;
        }
    }

    // It has been decided that the vCPU should be run.
    (*vcpu).cpu = (*current).cpu;
    (*vcpu).state = VCpuStatus::Running;

    // Mark the registers as unavailable now that we're about to reflect them
    // onto the real registers. This will also prevent another physical CPU
    // from trying to read these registers.
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
) -> u64 {
    let vm;
    let vcpu;
    let mut ret = HfVCpuRunReturn::WaitForInterrupt { ns: HF_SLEEP_INDEFINITE };

    // Only the primary VM can switch vcpus.
    if (*(*current).vm).id != HF_PRIMARY_VM_ID {
        return hf_vcpu_run_return_encode(ret);
    }

    // Only the secondary VM vcpus can be run.
    if vm_id == HF_PRIMARY_VM_ID {
        return hf_vcpu_run_return_encode(ret);
    }

    // The requested VM must exist.
    vm = vm_find(vm_id);
    if vm == ptr::null_mut() {
        return hf_vcpu_run_return_encode(ret);
    }

    // The requested vcpu must exist.
    if vcpu_idx >= (*vm).vcpu_count {
        return hf_vcpu_run_return_encode(ret);
    }

    // Update state if allowed.
    vcpu = vm_get_vcpu(vm, vcpu_idx);
    if !api_vcpu_prepare_run(current, vcpu, &mut ret) {
        return hf_vcpu_run_return_encode(ret);
    }

    // Inject timer interrupt if timer has expired. It's safe to access
    // vcpu->regs here because api_vcpu_prepare_run already made sure that
    // regs_available was true (and then set it to false) before returning
    // true.
    if arch_timer_pending(&mut (*vcpu).regs) {
        // Make virtual timer interrupt pending.
        internal_interrupt_inject(vcpu, HF_VIRTUAL_TIMER_INTID, vcpu, ptr::null_mut());

        // Set the mask bit so the hardware interrupt doesn't fire again.
        // Ideally we wouldn't do this because it affects what the secondary
        // vcPU sees, but if we don't then we end up with a loop of the
        // interrupt firing each time we try to return to the secondary vCPU.
        arch_timer_mask(&mut (*vcpu).regs);
    }

    // Switch to the vcpu.
    *next = vcpu;

    // Set a placeholder return code to the scheduler. This will be overwritten
    // when the switch back to the primary occurs.
    ret = HfVCpuRunReturn::Preempted;

    return hf_vcpu_run_return_encode(ret);
}

/// Check that the mode indicates memory that is vaid, owned and exclusive.
fn api_mode_valid_owned_and_exclusive(mode: Mode) -> bool {
    (mode & (Mode::INVALID | Mode::UNOWNED | Mode::SHARED)).is_empty()
}

/// Determines the value to be returned by api_vm_configure and
/// api_mailbox_clear after they've succeeded. If a secondary VM is running and
/// there are waiters, it also switches back to the primary VM for it to wake
/// waiters up.
unsafe fn api_waiter_result(locked_vm: VmLocked, current: *mut VCpu, next: *mut *mut VCpu) -> i64 {
    let vm = locked_vm.vm;
    let ret = HfVCpuRunReturn::NotifyWaiters;

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
        Mode::R,
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
        Mode::W,
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
    orig_send_mode: Mode,
    pa_recv_begin: paddr_t,
    pa_recv_end: paddr_t,
    orig_recv_mode: Mode,
) -> bool {
    let ret;
    let mut local_page_pool: MPool = mem::uninitialized();

    // Create a local pool so any freed memory can't be used by another thread.
    // This is to ensure the original mapping can be restored if any stage of
    // the process fails.
    mpool_init_with_fallback(&mut local_page_pool, API_PAGE_POOL.get_ref());

    // Take memory ownership away from the VM and mark as shared.
    if !mm_vm_identity_map(
        &mut (*vm_locked.vm).ptable,
        pa_send_begin,
        pa_send_end,
        (Mode::UNOWNED | Mode::SHARED | Mode::R | Mode::W),
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
        (Mode::UNOWNED | Mode::SHARED | Mode::R),
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

    // The following mappings will not require more memory than is available in
    // the local pool.
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

    // Ensure the pages are valid, owned and exclusive to the VM and that the
    // VM has the required access to the memory.
    if !mm_vm_get_mode(
        &mut (*vm).ptable,
        send,
        ipa_add(send, PAGE_SIZE),
        &mut orig_send_mode,
    ) || !api_mode_valid_owned_and_exclusive(orig_send_mode)
        || !orig_send_mode.contains(Mode::R)
        || !orig_send_mode.contains(Mode::W)
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
        || !orig_recv_mode.contains(Mode::R)
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
    attributes: SpciMsgSendAttributes,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> SpciReturn {
    let from = (*current).vm;

    // TODO: Refactor the control flow of this function, and make this variable
    // immutable.
    let mut ret;

    let notify = attributes.contains(SpciMsgSendAttributes::NOTIFY);

    // Check that the sender has configured its send buffer. Copy the message
    // header. If the tx mailbox at from_msg is configured (i.e.
    // from_msg != ptr::null()) then it can be safely accessed after releasing
    // the lock since the tx mailbox address can only be configured once.
    sl_lock(&(*from).lock);
    let from_msg = (*from).mailbox.send;
    sl_unlock(&(*from).lock);

    if from_msg == ptr::null() {
        return SpciReturn::InvalidParameters;
    }

    // Note that the payload is not copied when the message header is.
    let mut from_msg_replica = ptr::read(from_msg);

    // Ensure source VM id corresponds to the current VM.
    if from_msg_replica.source_vm_id != (*from).id {
        return SpciReturn::InvalidParameters;
    }

    let size = from_msg_replica.length as usize;
    // Limit the size of transfer.
    if size > SPCI_MSG_PAYLOAD_MAX {
        return SpciReturn::InvalidParameters;
    }

    // Disallow reflexive requests as this suggests an error in the VM.
    if from_msg_replica.target_vm_id == (*from).id {
        return SpciReturn::InvalidParameters;
    }

    // Ensure the target VM exists.
    let to = vm_find(from_msg_replica.target_vm_id);
    if to == ptr::null_mut() {
        return SpciReturn::InvalidParameters;
    }

    // Hf needs to hold the lock on `to` before the mailbox state is checked.
    // The lock on `to` must be held until the information is copied to `to` Rx
    // buffer. Since in spci_msg_handle_architected_message we may call
    // api_spci_share_memory which must hold the `from` lock, we must hold the
    // `from` lock at this point to prevent a deadlock scenario.
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

        ret = SpciReturn::Busy;
        // goto out;
        vm_unlock(&mut vm_from_to_lock.vm1);
        vm_unlock(&mut vm_from_to_lock.vm2);

        return ret;
    }

    let to_msg = (*to).mailbox.recv;

    // Handle architected messages.
    if !from_msg_replica.flags.contains(SpciMessageFlags::IMPDEF) {
        // Buffer holding the internal copy of the shared memory regions.
        // TODO: Buffer is temporarily in the stack.
        let mut message_buffer: [u8; mem::size_of::<SpciArchitectedMessageHeader>()
            + mem::size_of::<SpciMemoryRegionConstituent>()
            + mem::size_of::<SpciMemoryRegion>()] = mem::uninitialized();

        let architected_header = spci_get_architected_message_header((*from).mailbox.send);

        if from_msg_replica.length as usize > message_buffer.len() {
            ret =SpciReturn::InvalidParameters;
            // goto out;
            vm_unlock(&mut vm_from_to_lock.vm1);
            vm_unlock(&mut vm_from_to_lock.vm2);

            return ret;
        }

        if (from_msg_replica.length as usize) < mem::size_of::<SpciArchitectedMessageHeader>() {
            ret = SpciReturn::InvalidParameters;
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
        // spci_msg_handle_architected_message. The execution flow commencing
        // at spci_msg_handle_architected_message will make several accesses to
        // fields in message_buffer. The memory area message_buffer must be
        // exclusively owned by Hf so that TOCTOU issues do not arise.
        ret = spci_msg_handle_architected_message(
            vm_from_to_lock.vm1,
            vm_from_to_lock.vm2,
            architected_message_replica,
            &mut from_msg_replica,
            to_msg,
        );

        if ret != SpciReturn::Success {
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


    let primary_ret = HfVCpuRunReturn::Message { vm_id: (*to).id };
    ret = SpciReturn::Success;

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

/// Receives a message from the mailbox. If one isn't available, this function
/// can optionally block the caller until one becomes available.
///
/// No new messages can be received until the mailbox has been cleared.
#[no_mangle]
pub unsafe extern "C" fn api_spci_msg_recv(
    attributes: SpciMsgRecvAttributes,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> SpciReturn {
    let vm = (*current).vm;
    let return_code: SpciReturn;
    let block = attributes.contains(SpciMsgRecvAttributes::BLOCK);

    // The primary VM will receive messages as a status code from running vcpus
    // and must not call this function.
    if (*vm).id == HF_PRIMARY_VM_ID {
        return SpciReturn::Interrupted;
    }

    sl_lock(&(*vm).lock);

    // Return pending messages without blocking.
    if (*vm).mailbox.state == MailboxState::Received {
        (*vm).mailbox.state = MailboxState::Read;
        return_code = SpciReturn::Success;
        // goto out;
        sl_unlock(&(*vm).lock);

        return return_code;
    }

    // No pending message so fail if not allowed to block.
    if !block {
        return_code = SpciReturn::Retry;
        // goto out;
        sl_unlock(&(*vm).lock);

        return return_code;
    }

    // From this point onward this call can only be interrupted or a message
    // received. If a message is received the return value will be set at that
    // time to SPCI_SUCCESS.
    return_code = SpciReturn::Interrupted;

    // Don't block if there are enabled and pending interrupts, to match
    // behaviour of wait_for_interrupt.
    if (*current).interrupts.enabled_and_pending_count > 0 {
        // goto out;
        sl_unlock(&(*vm).lock);

        return return_code;
    }

    // Switch back to primary vm to block.
    {
        let run_return = HfVCpuRunReturn::WaitForMessage {
            ns: mem::uninitialized(),
        };

        *next = api_switch_to_primary(current, run_return, VCpuStatus::BlockedMailbox);
    }

    // out:
    sl_unlock(&(*vm).lock);

    return return_code;
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
pub unsafe extern "C" fn api_mailbox_writable_get(current: *const VCpu) -> i64 {
    let vm = (*current).vm;
    let ret;

    sl_lock(&(*vm).lock);
    if list_empty(&(*vm).mailbox.ready_list) {
        ret = -1;
        // goto exit;
        sl_unlock(&(*vm).lock);
        return ret;
    }

    let entry: *mut WaitEntry =
        container_of!((*vm).mailbox.ready_list.next, WaitEntry, ready_links);
    list_remove(&mut (*entry).ready_links);
    ret = entry.offset_from((*vm).wait_entries.as_ptr()) as i64;

    // exit:
    sl_unlock(&(*vm).lock);
    return ret;
}

/// Retrieves the next VM waiting to be notified that the mailbox of the
/// specified VM became writable. Only primary VMs are allowed to call this.
///
/// Returns -1 on failure or if there are no waiters; the VM id of the next
/// waiter otherwise.
#[no_mangle]
pub unsafe extern "C" fn api_mailbox_waiter_get(vm_id: spci_vm_id_t, current: *const VCpu) -> i64 {
    // Only primary VMs are allowed to call this function.
    if (*(*current).vm).id != HF_PRIMARY_VM_ID {
        return -1;
    }

    let vm = vm_find(vm_id);
    if vm == ptr::null_mut() {
        return -1;
    }

    // Check if there are outstanding notifications from given vm.
    let mut locked = vm_lock(vm);
    let entry = api_fetch_waiter(locked);
    vm_unlock(&mut locked);

    if entry == ptr::null_mut() {
        return -1;
    }

    // Enqueue notification to waiting VM.
    let waiting_vm = (*entry).waiting_vm as *mut Vm;

    sl_lock(&(*waiting_vm).lock);
    if list_empty(&(*entry).ready_links) {
        list_append(
            &mut (*waiting_vm).mailbox.ready_list,
            &mut (*entry).ready_links,
        );
    }
    sl_unlock(&(*waiting_vm).lock);

    (*waiting_vm).id as i64
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
pub unsafe extern "C" fn api_mailbox_clear(current: *mut VCpu, next: *mut *mut VCpu) -> i64 {
    let vm = (*current).vm;
    let ret;
    let mut locked = vm_lock(vm);
    match (*vm).mailbox.state {
        MailboxState::Empty => {
            ret = 0;
        }
        MailboxState::Received => {
            ret = -1;
        }
        MailboxState::Read => {
            ret = api_waiter_result(locked, current, next);
            (*vm).mailbox.state = MailboxState::Empty;
        }
    }

    vm_unlock(&mut locked);
    ret
}

/// Enables or disables a given interrupt ID for the calling vCPU.
///
/// Returns 0 on success, or -1 if the intid is invalid.
#[no_mangle]
pub unsafe extern "C" fn api_interrupt_enable(intid: u32, enable: bool, current: *mut VCpu) -> i64 {
    let intid_index = (intid as usize) / INTERRUPT_REGISTER_BITS;
    let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS as u32);

    if intid as usize >= HF_NUM_INTIDS {
        return -1;
    }

    sl_lock(&(*current).lock);
    if enable {
        // If it is pending and was not enabled before, increment the count.
        if ((*current).interrupts.pending[intid_index]
            & !(*current).interrupts.enabled[intid_index]
            & intid_mask)
            != 0
        {
            (*current).interrupts.enabled_and_pending_count += 1;
        }
        (*current).interrupts.enabled[intid_index] |= intid_mask;
    } else {
        // If it is pending and was enabled before, decrement the count.
        if ((*current).interrupts.pending[intid_index]
            & (*current).interrupts.enabled[intid_index]
            & intid_mask)
            != 0
        {
            (*current).interrupts.enabled_and_pending_count -= 1;
        }
        (*current).interrupts.enabled[intid_index] &= !intid_mask;
    }

    sl_unlock(&(*current).lock);
    0
}

/// Returns the ID of the next pending interrupt for the calling vCPU, and
/// acknowledges it (i.e. marks it as no longer pending). Returns
/// HF_INVALID_INTID if there are no pending interrupts.
#[no_mangle]
pub unsafe extern "C" fn api_interrupt_get(current: *mut VCpu) -> u32 {
    let mut first_interrupt = HF_INVALID_INTID;

    // Find the first enabled pending interrupt ID, returns it, and
    // deactive it.
    sl_lock(&(*current).lock);
    for i in 0..(HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS) {
        let enabled_and_pending =
            (*current).interrupts.enabled[i] & (*current).interrupts.pending[i];
        if enabled_and_pending != 0 {
            let bit_index = enabled_and_pending.trailing_zeros();

            // Mark it as no longer pending and decrement the count.
            (*current).interrupts.pending[i] &= !(1u32 << bit_index);
            (*current).interrupts.enabled_and_pending_count -= 1;
            first_interrupt = (i * INTERRUPT_REGISTER_BITS) as u32 + bit_index;
            break;
        }
    }

    sl_unlock(&(*current).lock);
    first_interrupt
}

/// Returns whether the current vCPU is allowed to inject an interrupt into the
/// given VM and vCPU.
#[inline]
unsafe fn is_injection_allowed(target_vm_id: spci_vm_id_t, current: *const VCpu) -> bool {
    let current_vm_id = (*(*current).vm).id;

    // The primary VM is allowed to inject interrupts into any VM. Secondary
    // VMs are only allowed to inject interrupts into their own vCPUs.
    current_vm_id == HF_PRIMARY_VM_ID || current_vm_id == target_vm_id
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
pub unsafe extern "C" fn api_interrupt_inject(
    target_vm_id: spci_vm_id_t,
    target_vcpu_idx: spci_vcpu_index_t,
    intid: u32,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> i64 {
    let target_vm = vm_find(target_vm_id);

    if intid as usize >= HF_NUM_INTIDS {
        return -1;
    }

    if target_vm == ptr::null_mut() {
        return -1;
    }

    if target_vcpu_idx >= (*target_vm).vcpu_count {
        // The requested vcpu must exist.
        return -1;
    }

    if !is_injection_allowed(target_vm_id, current) {
        return -1;
    }

    let target_vcpu = vm_get_vcpu(target_vm, target_vcpu_idx);

    dlog!(
        "Injecting IRQ {} for VM {} VCPU {} from VM {} VCPU {}\n",
        intid,
        target_vm_id,
        target_vcpu_idx,
        (*(*current).vm).id,
        (*(*current).cpu).id
    );
    internal_interrupt_inject(target_vcpu, intid, current, next)
}

/// Clears a region of physical memory by overwriting it with zeros. The data is
/// flushed from the cache so the memory has been cleared across the system.
unsafe fn api_clear_memory(begin: paddr_t, end: paddr_t, ppool: *mut MPool) -> bool {
    // TODO: change this to a cpu local single page window rather than a global
    //       mapping of the whole range. Such an approach will limit the
    //       changes to stage-1 tables and will allow only local invalidation.

    let ret;
    let mut stage1_locked = mm_lock_stage1();
    // TODO: Refactor result variable name.
    // But mm_identity_map returns begin if succeed or null pointer otherwise.
    // Hence the name is not important.
    let ptr_ = mm_identity_map(stage1_locked, begin, end, Mode::W, ppool);
    let size = pa_difference(begin, end);

    if ptr_ == ptr::null_mut() {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        mm_defrag(stage1_locked, ppool);
        // goto fail;
        ret = false;
        mm_unlock_stage1(&mut stage1_locked);
        return ret;
    }

    memset_s(ptr_ as usize as _, size, 0, size);
    arch_mm_write_back_dcache(ptr_ as usize, size);
    mm_unmap(stage1_locked, begin, end, ppool);

    ret = true;
    // goto out;
    mm_unlock_stage1(&mut stage1_locked);
    return ret;

    // fail:
    ret = false;

    // out:
    mm_unlock_stage1(&mut stage1_locked);
    ret
}

// TODO: Move function to spci_architectted_message.c. (How in Rust?)
/// Shares memory from the calling VM with another. The memory can be shared in
/// different modes.
///
/// This function requires the calling context to hold the <to> and <from>
/// locks.
///
/// Returns:
///  In case of error one of the following values is returned:
///   1) SPCI_INVALID_PARAMETERS - The endpoint provided parameters were
///     erroneous;
///   2) SPCI_NO_MEMORY - Hf did not have sufficient memory to complete
///     the request.
///  Success is indicated by SPCI_SUCCESS.
#[no_mangle]
pub unsafe extern "C" fn api_spci_share_memory(
    to_locked: VmLocked,
    from_locked: VmLocked,
    memory_region: *mut SpciMemoryRegion,
    memory_to_attributes: u32,
    share: usize,
) -> SpciReturn {
    let to = to_locked.vm;
    let from = from_locked.vm;
    let ret;

    // Disallow reflexive shares as this suggests an error in the VM.
    if to == from {
        return SpciReturn::InvalidParameters;
    }

    // Create a local pool so any freed memory can't be used by another thread.
    // This is to ensure the original mapping can be restored if any stage of
    // the process fails.
    let mut local_page_pool: MPool = mem::uninitialized();
    mpool_init_with_fallback(&mut local_page_pool, API_PAGE_POOL.get_ref());

    // Obtain the single contiguous set of pages from the memory_region.
    // TODO: Add support for multiple constituent regions.
    let constituent =
        &(*memory_region).constituents as *const _ as usize as *const SpciMemoryRegionConstituent;
    let size = (*constituent).page_count as usize * PAGE_SIZE;
    let begin = ipa_init((*constituent).address as usize);
    let end = ipa_add(begin, size as usize);

    // Check if the state transition is lawful for both VMs involved in the
    // memory exchange, ensure that all constituents of a memory region being
    // shared are at the same state.
    let mut orig_from_mode = mem::uninitialized();
    let mut from_mode = mem::uninitialized();
    let mut to_mode = mem::uninitialized();
    let share = match share {
        0x2 => SpciMemoryShare::Donate,
        _ => return SpciReturn::InvalidParameters,
    };

    if !spci_msg_check_transition(
        to,
        from,
        share,
        &mut orig_from_mode,
        begin,
        end,
        memory_to_attributes,
        &mut from_mode,
        &mut to_mode,
    ) {
        return SpciReturn::InvalidParameters;
    }

    let pa_begin = pa_from_ipa(begin);
    let pa_end = pa_from_ipa(end);

    // First update the mapping for the sender so there is not overlap with the
    // recipient.
    if !mm_vm_identity_map(
        &mut (*from).ptable,
        pa_begin,
        pa_end,
        from_mode,
        ptr::null_mut(),
        &mut local_page_pool,
    ) {
        ret = SpciReturn::NoMemory;
        // goto out;
        mpool_fini(&mut local_page_pool);
        return ret;
    }

    // Complete the transfer by mapping the memory into the recipient.
    if !mm_vm_identity_map(
        &mut (*to).ptable,
        pa_begin,
        pa_end,
        to_mode,
        ptr::null_mut(),
        &mut local_page_pool,
    ) {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        mm_vm_defrag(&mut (*from).ptable, &mut local_page_pool);

        ret = SpciReturn::NoMemory;

        assert!(mm_vm_identity_map(
            &mut (*from).ptable,
            pa_begin,
            pa_end,
            orig_from_mode,
            ptr::null_mut(),
            &mut local_page_pool
        ));
        // goto out;
        mpool_fini(&mut local_page_pool);
        return ret;
    }

    ret = SpciReturn::Success;

    // out:
    mpool_fini(&mut local_page_pool);
    return ret;
}

/// Shares memory from the calling VM with another. The memory can be shared in
/// different modes.
///
/// TODO: the interface for sharing memory will need to be enhanced to allow
///       sharing with different modes e.g. read-only, informing the recipient
///       of the memory they have been given, opting to not wipe the memory and
///       possibly allowing multiple blocks to be transferred. What this will
///       look like is TBD.
#[no_mangle]
pub unsafe extern "C" fn api_share_memory(
    vm_id: spci_vm_id_t,
    addr: ipaddr_t,
    size: size_t,
    share: usize,
    current: *mut VCpu,
) -> i64 {
    let from = (*current).vm;

    // Disallow reflexive shares as this suggests an error in the VM.
    if vm_id == (*from).id {
        assert!(false);
        return -1;
    }

    // Ensure the target VM exists.
    let to = vm_find(vm_id);
    if to == ptr::null_mut() {
        return -1;
    }

    let begin = addr;
    let end = ipa_add(addr, size);

    // Fail if addresses are not page-aligned.
    if !is_aligned(ipa_addr(begin), PAGE_SIZE) || !is_aligned(ipa_addr(end), PAGE_SIZE) {
        return -1;
    }

    // Convert the sharing request to memory management modes.
    let share = match share {
        0 => HfShare::Give,
        1 => HfShare::Lend,
        2 => HfShare::Share,
        _ => {
            // The input is untrusted so might not be a valid value.
            return -1;
        }
    };

    let (from_mode, to_mode) = match share {
        HfShare::Give => (
            (Mode::INVALID | Mode::UNOWNED),
            (Mode::R | Mode::W | Mode::X)
        ),
        HfShare::Lend => (
            Mode::INVALID,
            (Mode::R | Mode::W | Mode::X | Mode::UNOWNED)
        ),
        HfShare::Share => (
            (Mode::R | Mode::W | Mode::X | Mode::SHARED),
            (Mode::R | Mode::W | Mode::X | Mode::UNOWNED | Mode::SHARED)
        ),
    };

    // Create a local pool so any freed memory can't be used by antoher thread.
    // This is to ensure the original mapping can be restored if any stage of
    // the process fails.
    // TODO: So that's reason why Hafnium use local_page_pool! We need to verify
    // this.
    let mut local_page_pool = mem::uninitialized();
    mpool_init_with_fallback(&mut local_page_pool, API_PAGE_POOL.get_ref());

    sl_lock_both(&(*from).lock, &(*to).lock);

    let ret;

    // Ensure that the memory range is mapped with the same mode so that
    // changes can be reverted if the process fails.
    let mut orig_from_mode = mem::uninitialized();
    if !mm_vm_get_mode(&mut (*from).ptable, begin, end, &mut orig_from_mode) {
        // goto fail;
        ret = -1;

        sl_unlock(&(*from).lock);
        sl_unlock(&(*to).lock);

        mpool_fini(&mut local_page_pool);

        return ret;
    }

    // Ensure the memory range is valid for the sender. If it isn't, the sender
    // has either shared it with another VM already or has no claim to the
    // memory.
    if orig_from_mode.contains(Mode::INVALID) {
        // goto fail;
        ret = -1;

        sl_unlock(&(*from).lock);
        sl_unlock(&(*to).lock);

        mpool_fini(&mut local_page_pool);

        return ret;
    }

    // The sender must own the memory and have exclusive access to it in order
    // to share it. Alternatively, it is giving memory back to the owning VM.
    if orig_from_mode.contains(Mode::UNOWNED) {
        let mut orig_to_mode = mem::uninitialized();

        if share != HfShare::Give
            || !mm_vm_get_mode(&mut (*to).ptable, begin, end, &mut orig_to_mode)
            || orig_to_mode.contains(Mode::UNOWNED)
        {
            // goto fail;
            ret = -1;

            sl_unlock(&(*from).lock);
            sl_unlock(&(*to).lock);

            mpool_fini(&mut local_page_pool);

            return ret;
        }
    } else if orig_from_mode.contains(Mode::SHARED) {
        // goto fail;
        ret = -1;

        sl_unlock(&(*from).lock);
        sl_unlock(&(*to).lock);

        mpool_fini(&mut local_page_pool);

        return ret;
    }

    let pa_begin = pa_from_ipa(begin);
    let pa_end = pa_from_ipa(end);

    // First update the mapping for the sender so there is not overlap with the
    // recipient.
    if !mm_vm_identity_map(
        &mut (*from).ptable,
        pa_begin,
        pa_end,
        from_mode,
        ptr::null_mut(),
        &mut local_page_pool,
    ) {
        // goto fail;
        ret = -1;

        sl_unlock(&(*from).lock);
        sl_unlock(&(*to).lock);

        mpool_fini(&mut local_page_pool);

        return ret;
    }

    // Clear the memory so no VM or device can see the previous contents.
    if !api_clear_memory(pa_begin, pa_end, &mut local_page_pool) {
        // goto fail_return_to_sender;
        assert!(mm_vm_identity_map(
            &mut (*from).ptable,
            pa_begin,
            pa_end,
            orig_from_mode,
            ptr::null_mut(),
            &mut local_page_pool
        ));

        ret = -1;

        sl_unlock(&(*from).lock);
        sl_unlock(&(*to).lock);

        mpool_fini(&mut local_page_pool);
        return ret;
    }

    // Complete the transfer by mapping the memory into the recipient.
    if !mm_vm_identity_map(
        &mut (*to).ptable,
        pa_begin,
        pa_end,
        to_mode,
        ptr::null_mut(),
        &mut local_page_pool,
    ) {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        mm_vm_defrag(&mut (*from).ptable, &mut local_page_pool);
        // goto fail_return_to_sender;
        assert!(mm_vm_identity_map(
            &mut (*from).ptable,
            pa_begin,
            pa_end,
            orig_from_mode,
            ptr::null_mut(),
            &mut local_page_pool
        ));

        // fail:
        ret = -1;

        // out:
        sl_unlock(&(*from).lock);
        sl_unlock(&(*to).lock);

        mpool_fini(&mut local_page_pool);
        return ret;
    }

    ret = 0;
    // goto out;
    sl_unlock(&(*from).lock);
    sl_unlock(&(*to).lock);

    mpool_fini(&mut local_page_pool);

    return ret;

    // fail_return_to_sender:
    assert!(mm_vm_identity_map(
        &mut (*from).ptable,
        pa_begin,
        pa_end,
        orig_from_mode,
        ptr::null_mut(),
        &mut local_page_pool
    ));

    // fail:
    ret = -1;

    // out:
    sl_unlock(&(*from).lock);
    sl_unlock(&(*to).lock);

    mpool_fini(&mut local_page_pool);

    return ret;
}

/// Returns the version of the implemented SPCI specification.
#[no_mangle]
pub unsafe extern "C" fn api_spci_version() -> i32 {
    // Ensure that both major and minor revision representation occupies at
    // most 15 bits.
    const_assert!(0x8000 > SPCI_VERSION_MAJOR);
    const_assert!(0x10000 > SPCI_VERSION_MINOR);

    (SPCI_VERSION_MAJOR << SPCI_VERSION_MAJOR_OFFSET) | SPCI_VERSION_MINOR
}

#[no_mangle]
pub unsafe extern "C" fn api_debug_log(c: c_char, current: *mut VCpu) -> i64 {
    let vm = (*current).vm;
    let mut vm_locked = vm_lock(vm);

    if c == '\n' as u32 as u8
        || c == '\0' as u32 as u8
        || (*vm).log_buffer_length == (*vm).log_buffer.len()
    {
        dlog_flush_vm_buffer(vm_locked);
    } else {
        (*vm).log_buffer[(*vm).log_buffer_length] = c;
        (*vm).log_buffer_length += 1;
    }

    vm_unlock(&mut vm_locked);
    0
}
