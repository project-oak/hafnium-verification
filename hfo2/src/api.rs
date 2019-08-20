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
// vcpu::execution_lock -> vm::lock -> vcpu::interrupts_lock -> mm_stage1_lock -> dlog sl
//
// Locks of the same kind require the lock of lowest address to be locked first, see
// `sl_lock_both()`.

// Currently, a page is mapped for the send and receive buffers so the maximum request is the size
// of a page.
const_assert_eq!(hf_mailbox_size; HF_MAILBOX_SIZE, PAGE_SIZE);

/// A global page pool for sharing memories. Its mutability is needed only for
/// initialization.
static mut API_PAGE_POOL: MaybeUninit<MPool> = MaybeUninit::uninit();

/// Initialises the API page pool by taking ownership of the contents of the
/// given page pool.
/// TODO(HfO2): The ownership of `ppool` is actually moved from `one_time_init`
/// to here. Refactor this function like `Api::new(ppool: MPool) -> Api`. (#31)
#[no_mangle]
pub unsafe extern "C" fn api_init(ppool: *const MPool) {
    API_PAGE_POOL = MaybeUninit::new(MPool::new_from(&*ppool));
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
        HfVCpuRunReturn::WaitForInterrupt { ns } | HfVCpuRunReturn::WaitForMessage { ns } => {
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
    arch_regs_set_retval(&mut (*next).regs, primary_ret.into_raw());

    // Mark the current vcpu as waiting.
    (*current).state = secondary_state;

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
        // `api_switch_to_primary` always initializes this variable.
        ns: HF_SLEEP_INDEFINITE,
    };

    api_switch_to_primary(current, ret, VCpuStatus::BlockedInterrupt)
}

/// Puts the current vCPU in off mode, and returns to the primary VM.
#[no_mangle]
pub unsafe extern "C" fn api_vcpu_off(current: *mut VCpu) -> *mut VCpu {
    let ret = HfVCpuRunReturn::WaitForInterrupt {
        // `api_switch_to_primary` always initializes this variable.
        ns: HF_SLEEP_INDEFINITE,
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
    if vm.is_null() {
        return 0;
    }

    (*vm).vcpu_count
}

/// This function is called by the architecture-specific context switching
/// function to indicate that register state for the given vcpu has been saved
/// and can therefore be used by other pcpus.
#[no_mangle]
pub unsafe extern "C" fn api_regs_state_saved(vcpu: *mut VCpu) {
    sl_unlock(&(*vcpu).execution_lock);
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
    intid: intid_t,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> i64 {
    let intid_index = intid as usize / INTERRUPT_REGISTER_BITS;
    let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS as u32);
    let mut ret: i64 = 0;

    sl_lock(&(*target_vcpu).interrupts_lock);

    // We only need to change state and (maybe) trigger a virtual IRQ if it
    // is enabled and was not previously pending. Otherwise we can skip
    // everything except setting the pending bit.
    //
    // If you change this logic make sure to update the need_vm_lock logic
    // above to match.
    if (*target_vcpu).interrupts.enabled[intid_index]
        & !(*target_vcpu).interrupts.pending[intid_index]
        & intid_mask
        == 0
    {
        // goto out;
        // Either way, make it pending.
        (*target_vcpu).interrupts.pending[intid_index] |= intid_mask;
        sl_unlock(&(*target_vcpu).interrupts_lock);
        return ret;
    }

    // Increment the count.
    (*target_vcpu).interrupts.enabled_and_pending_count += 1;

    // Only need to update state if there was not already an interrupt enabled
    // and pending.
    if (*target_vcpu).interrupts.enabled_and_pending_count != 1 {
        // goto out;
        // Either way, make it pending.
        (*target_vcpu).interrupts.pending[intid_index] |= intid_mask;
        sl_unlock(&(*target_vcpu).interrupts_lock);
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
    (*target_vcpu).interrupts.pending[intid_index] |= intid_mask;
    sl_unlock(&(*target_vcpu).interrupts_lock);
    return ret;
}

/// Prepares the vcpu to run by updating its state and fetching whether a return
/// value needs to be forced onto the vCPU.
///
/// Returns:
///  - false if it fails to prepare `vcpu` to run.
///  - true if it succeeds to prepare `vcpu` to run. In this case,
///    `vcpu.execution_lock` has acquired.
unsafe fn api_vcpu_prepare_run(
    current: *const VCpu,
    vcpu: *mut VCpu,
    run_ret: *mut HfVCpuRunReturn,
) -> bool {
    let ret;

    if !sl_try_lock(&(*vcpu).execution_lock) {
        // vCPU is running or prepared to run on another pCPU.
        //
        // It's ok not to return the sleep duration here because the other
        // physical CPU that is currently running this vCPU will return the
        // sleep duration if needed. The default return value is
        // HfVCpuRunReturn::WaitForInterrupt, so no need to set it explicitly.
        return false;
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

        if !ret {
            sl_unlock(&(*vcpu).execution_lock);
        }

        return ret;
    }

    match (*vcpu).state {
        VCpuStatus::Off | VCpuStatus::Aborted => {
            ret = false;

            if !ret {
                sl_unlock(&(*vcpu).execution_lock);
            }

            return ret;
        }

        // A pending message allows the vCPU to run so the message can be
        // delivered directly.
        // The VM needs to be locked to deliver mailbox messages.
        // The VM lock is not needed in the common case so it must only be taken
        // when it is going to be needed. This ensures there are no inter-vCPU
        // dependencies in the common run case meaning the sensitive context
        // switch performance is consistent.
        VCpuStatus::BlockedMailbox if (*(*vcpu).vm).inner.lock().try_read() => {
            arch_regs_set_retval(&mut (*vcpu).regs, SpciReturn::Success as uintreg_t);
        }

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

            if !ret {
                sl_unlock(&(*vcpu).execution_lock);
            }

            return ret;
        }

        VCpuStatus::Ready => {
            // break;
        }
    }

    // It has been decided that the vCPU should be run.
    (*vcpu).cpu = (*current).cpu;

    ret = true;

    if !ret {
        sl_unlock(&(*vcpu).execution_lock);
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
    let mut ret = HfVCpuRunReturn::WaitForInterrupt {
        ns: HF_SLEEP_INDEFINITE,
    };

    // Only the primary VM can switch vcpus.
    if (*(*current).vm).id != HF_PRIMARY_VM_ID {
        return ret.into_raw();
    }

    // Only the secondary VM vcpus can be run.
    if vm_id == HF_PRIMARY_VM_ID {
        return ret.into_raw();
    }

    // The requested VM must exist.
    vm = vm_find(vm_id);
    if vm.is_null() {
        return ret.into_raw();
    }

    // The requested vcpu must exist.
    if vcpu_idx >= (*vm).vcpu_count {
        return ret.into_raw();
    }

    // Update state if allowed.
    vcpu = vm_get_vcpu(vm, vcpu_idx);
    if !api_vcpu_prepare_run(current, vcpu, &mut ret) {
        return ret.into_raw();
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

    return ret.into_raw();
}

/// Determines the value to be returned by api_vm_configure and
/// api_mailbox_clear after they've succeeded. If a secondary VM is running and
/// there are waiters, it also switches back to the primary VM for it to wake
/// waiters up.
unsafe fn waiter_result(
    vm_id: spci_vm_id_t,
    vm_inner: &VmInner,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> i64 {
    let ret = HfVCpuRunReturn::NotifyWaiters;

    if vm_inner.is_waiter_list_empty() {
        // No waiters, nothing else to do.
        return 0;
    }

    if vm_id == HF_PRIMARY_VM_ID {
        // The caller is the primary VM. Tell it to wake up waiters.
        return 1;
    }

    // Switch back to the primary VM, informing it that there are waiters
    // that need to be notified.
    *next = api_switch_to_primary(current, ret, VCpuStatus::Ready);

    0
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

    // The hypervisor's memory map must be locked for the duration of this
    // operation to ensure there will be sufficient memory to recover from
    // any failures.
    //
    // TODO: the scope of the can be reduced but will require restructing
    //       to keep a single unlock point.
    let mut vm_inner = (*vm).inner.lock();
    if vm_inner
        .configure(send, recv, API_PAGE_POOL.get_ref())
        .is_none()
    {
        return -1;
    }

    // Tell caller about waiters, if any.
    waiter_result((*vm).id, &vm_inner, current, next)
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
    let from_msg = (*from).inner.lock().get_send_ptr();

    if from_msg.is_null() {
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
    if to.is_null() {
        return SpciReturn::InvalidParameters;
    }

    // Hf needs to hold the lock on `to` before the mailbox state is checked.
    // The lock on `to` must be held until the information is copied to `to` Rx
    // buffer. Since in spci_msg_handle_architected_message we may call
    // api_spci_share_memory which must hold the `from` lock, we must hold the
    // `from` lock at this point to prevent a deadlock scenario.
    let (mut to_state, mut from_state) = SpinLock::lock_both(&(*to).inner, &(*from).inner);

    if !to_state.is_empty() || !to_state.is_configured() {
        // Fail if the target isn't currently ready to receive data,
        // setting up for notification if requested.
        if notify {
            from_state.wait(&mut to_state, (*to).id);
        }

        return SpciReturn::Busy;
    }

    let to_msg = to_state.get_recv_ptr();

    // Handle architected messages.
    if !from_msg_replica.flags.contains(SpciMessageFlags::IMPDEF) {
        // Buffer holding the internal copy of the shared memory regions.
        // TODO: Buffer is temporarily in the stack.
        let mut message_buffer: [u8; mem::size_of::<SpciArchitectedMessageHeader>()
            + mem::size_of::<SpciMemoryRegionConstituent>()
            + mem::size_of::<SpciMemoryRegion>()] = mem::uninitialized();

        let architected_header = spci_get_architected_message_header(from_msg);

        if from_msg_replica.length as usize > message_buffer.len() {
            return SpciReturn::InvalidParameters;
        }

        if (from_msg_replica.length as usize) < mem::size_of::<SpciArchitectedMessageHeader>() {
            return SpciReturn::InvalidParameters;
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
            VmLocked { vm: to },
            VmLocked { vm: from },
            architected_message_replica,
            &mut from_msg_replica,
            to_msg,
        );

        if ret != SpciReturn::Success {
            return ret;
        }
    } else {
        // Copy data.
        memcpy_s(
            &mut (*to_msg).payload as *mut _ as usize as _,
            SPCI_MSG_PAYLOAD_MAX,
            // HfO2: below was &(*(*from).mailbox.send).payload, but we can
            // safely assume it is equal to &(*from_msg).payload, even though
            // from_msg was defined before entering critical section. That's
            // because we do not allow vm to be configured more than once.
            &(*from_msg).payload as *const _ as usize as _,
            size,
        );
        *to_msg = from_msg_replica;
    }

    let primary_ret = HfVCpuRunReturn::Message { vm_id: (*to).id };
    ret = SpciReturn::Success;

    // Messages for the primary VM are delivered directly.
    if (*to).id == HF_PRIMARY_VM_ID {
        to_state.set_read();
        *next = api_switch_to_primary(current, primary_ret, VCpuStatus::Ready);
        return ret;
    }

    to_state.set_received();

    // Return to the primary VM directly or with a switch.
    if (*from).id != HF_PRIMARY_VM_ID {
        *next = api_switch_to_primary(current, primary_ret, VCpuStatus::Ready);
    }

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
    let vm = &*(*current).vm;
    let return_code: SpciReturn;
    let block = attributes.contains(SpciMsgRecvAttributes::BLOCK);

    // The primary VM will receive messages as a status code from running vcpus
    // and must not call this function.
    if vm.id == HF_PRIMARY_VM_ID {
        return SpciReturn::Interrupted;
    }

    let mut vm_inner = vm.inner.lock();

    // Return pending messages without blocking.
    if vm_inner.try_read() {
        return SpciReturn::Success;
    }

    // No pending message so fail if not allowed to block.
    if !block {
        return SpciReturn::Retry;
    }

    // From this point onward this call can only be interrupted or a message
    // received. If a message is received the return value will be set at that
    // time to SPCI_SUCCESS.
    return_code = SpciReturn::Interrupted;

    // Don't block if there are enabled and pending interrupts, to match
    // behaviour of wait_for_interrupt.
    if (*current).interrupts.enabled_and_pending_count > 0 {
        return return_code;
    }

    // Switch back to primary vm to block.
    {
        let run_return = HfVCpuRunReturn::WaitForMessage {
            // `api_switch_to_primary` always initializes this variable.
            ns: HF_SLEEP_INDEFINITE,
        };

        *next = api_switch_to_primary(current, run_return, VCpuStatus::BlockedMailbox);
    }

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
    let mut vm_inner = (*vm).inner.lock();

    match vm_inner.dequeue_ready_list() {
        Some(id) => id as i64,
        None => -1,
    }
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
    if vm.is_null() {
        return -1;
    }

    // Check if there are outstanding notifications from given vm.
    let entry = (*vm).inner.lock().fetch_waiter();

    if entry.is_null() {
        return -1;
    }

    // Enqueue notification to waiting VM.
    // TODO: Is ready_list indeed a queue? I think API module treating it like
    // a stack.
    let waiting_vm = (*entry).waiting_vm;

    let mut vm_inner = (*waiting_vm).inner.lock();
    if list_empty(&(*entry).ready_links) {
        vm_inner.enqueue_ready_list(&mut *entry);
    }

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
    let mut vm_inner = (*vm).inner.lock();
    match vm_inner.get_state() {
        MailboxState::Empty => {
            ret = 0;
        }
        MailboxState::Received => {
            ret = -1;
        }
        MailboxState::Read => {
            ret = waiter_result((*vm).id, &vm_inner, current, next);
            vm_inner.set_empty();
        }
    }

    ret
}

/// Enables or disables a given interrupt ID for the calling vCPU.
///
/// Returns 0 on success, or -1 if the intid is invalid.
#[no_mangle]
pub unsafe extern "C" fn api_interrupt_enable(
    intid: intid_t,
    enable: bool,
    current: *mut VCpu,
) -> i64 {
    let intid_index = intid as usize / INTERRUPT_REGISTER_BITS;
    let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS as u32);

    if intid >= HF_NUM_INTIDS {
        return -1;
    }

    sl_lock(&(*current).interrupts_lock);
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

    sl_unlock(&(*current).interrupts_lock);
    0
}

/// Returns the ID of the next pending interrupt for the calling vCPU, and
/// acknowledges it (i.e. marks it as no longer pending). Returns
/// HF_INVALID_INTID if there are no pending interrupts.
#[no_mangle]
pub unsafe extern "C" fn api_interrupt_get(current: *mut VCpu) -> intid_t {
    let mut first_interrupt = HF_INVALID_INTID;

    // Find the first enabled pending interrupt ID, returns it, and
    // deactive it.
    sl_lock(&(*current).interrupts_lock);
    for i in 0..(HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS) {
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

    sl_unlock(&(*current).interrupts_lock);
    first_interrupt
}

/// Returns whether the current vCPU is allowed to inject an interrupt into the
/// given VM and vCPU.
#[inline]
fn is_injection_allowed(target_vm_id: spci_vm_id_t, current: &VCpu) -> bool {
    let current_vm_id = unsafe { (*current.vm).id };

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
    intid: intid_t,
    current: *mut VCpu,
    next: *mut *mut VCpu,
) -> i64 {
    let target_vm = vm_find(target_vm_id);

    if intid >= HF_NUM_INTIDS {
        return -1;
    }

    if target_vm.is_null() {
        return -1;
    }

    if target_vcpu_idx >= (*target_vm).vcpu_count {
        // The requested vcpu must exist.
        return -1;
    }

    if !is_injection_allowed(target_vm_id, &*current) {
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
fn clear_memory(begin: paddr_t, end: paddr_t, ppool: &MPool) -> bool {
    let mut hypervisor_ptable = HYPERVISOR_PAGE_TABLE.lock();
    let size = pa_difference(begin, end);
    let region = pa_addr(begin);

    // TODO: change this to a cpu local single page window rather than a global
    //       mapping of the whole range. Such an approach will limit the
    //       changes to stage-1 tables and will allow only local invalidation.

    if let None = hypervisor_ptable.identity_map(begin, end, Mode::W, ppool) {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        hypervisor_ptable.defrag(ppool);
        return false;
    }

    unsafe {
        memset_s(region as usize as _, size, 0, size);
        arch_mm_write_back_dcache(region as usize, size);
    }

    hypervisor_ptable.unmap(begin, end, ppool);

    true
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
    let to_state = (*to_locked.vm).inner.get_mut_unchecked();
    let from_state = (*from_locked.vm).inner.get_mut_unchecked();

    // Disallow reflexive shares as this suggests an error in the VM.
    if to_locked.vm == from_locked.vm {
        return SpciReturn::InvalidParameters;
    }

    // Create a local pool so any freed memory can't be used by another thread.
    // This is to ensure the original mapping can be restored if any stage of
    // the process fails.
    let local_page_pool: MPool = MPool::new_with_fallback(API_PAGE_POOL.get_ref());

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
        to_locked.vm,
        from_locked.vm,
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
    if from_state
        .ptable
        .identity_map(pa_begin, pa_end, from_mode, &local_page_pool)
        .is_none()
    {
        return SpciReturn::NoMemory;
    }

    // Complete the transfer by mapping the memory into the recipient.
    if to_state
        .ptable
        .identity_map(pa_begin, pa_end, to_mode, &local_page_pool)
        .is_none()
    {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        from_state.ptable.defrag(&local_page_pool);

        assert!(from_state
            .ptable
            .identity_map(pa_begin, pa_end, orig_from_mode, &local_page_pool)
            .is_some());

        return SpciReturn::NoMemory;
    }

    SpciReturn::Success
}

/// Shares memory from the calling VM with another. The memory can be shared in
/// different modes.
///
/// TODO: the interface for sharing memory will need to be enhanced to allow
///       sharing with different modes e.g. read-only, informing the recipient
///       of the memory they have been given, opting to not wipe the memory and
///       possibly allowing multiple blocks to be transferred. What this will
///       look like is TBD.
fn share_memory(
    vm_id: spci_vm_id_t,
    addr: ipaddr_t,
    size: usize,
    share: HfShare,
    current: &VCpu,
) -> Option<()> {
    let from: &Vm = unsafe { &*current.vm };

    // Disallow reflexive shares as this suggests an error in the VM.
    if vm_id == from.id {
        assert!(false);
        return None;
    }

    // Ensure the target VM exists.
    let to = unsafe { vm_find(vm_id) };
    if to.is_null() {
        return None;
    }

    let to = unsafe { &*to };

    let begin = addr;
    let end = ipa_add(addr, size);

    // Fail if addresses are not page-aligned.
    if !is_aligned(ipa_addr(begin), PAGE_SIZE) || !is_aligned(ipa_addr(end), PAGE_SIZE) {
        return None;
    }

    let (from_mode, to_mode) = match share {
        HfShare::Give => (
            (Mode::INVALID | Mode::UNOWNED),
            (Mode::R | Mode::W | Mode::X),
        ),
        HfShare::Lend => (Mode::INVALID, (Mode::R | Mode::W | Mode::X | Mode::UNOWNED)),
        HfShare::Share => (
            (Mode::R | Mode::W | Mode::X | Mode::SHARED),
            (Mode::R | Mode::W | Mode::X | Mode::UNOWNED | Mode::SHARED),
        ),
    };

    // Create a local pool so any freed memory can't be used by another thread.
    // This is to ensure the original mapping can be restored if any stage of
    // the process fails.
    // TODO: So that's reason why Hafnium use local_page_pool! We need to verify
    // this.
    let local_page_pool = MPool::new_with_fallback(unsafe { API_PAGE_POOL.get_ref() });

    let (mut from_state, mut to_state) = SpinLock::lock_both(&(*from).inner, &(*to).inner);

    // Ensure that the memory range is mapped with the same mode so that
    // changes can be reverted if the process fails.
    let orig_from_mode = from_state.ptable.get_mode(begin, end)?;

    // Ensure the memory range is valid for the sender. If it isn't, the sender
    // has either shared it with another VM already or has no claim to the
    // memory.
    if orig_from_mode.contains(Mode::INVALID) {
        return None;
    }

    // The sender must own the memory and have exclusive access to it in order
    // to share it. Alternatively, it is giving memory back to the owning VM.
    if orig_from_mode.contains(Mode::UNOWNED) {
        let orig_to_mode = to_state.ptable.get_mode(begin, end)?;

        if share != HfShare::Give || orig_to_mode.contains(Mode::UNOWNED) {
            return None;
        }
    } else if orig_from_mode.contains(Mode::SHARED) {
        return None;
    }

    let pa_begin = pa_from_ipa(begin);
    let pa_end = pa_from_ipa(end);

    // First update the mapping for the sender so there is not overlap with the
    // recipient.
    from_state
        .ptable
        .identity_map(pa_begin, pa_end, from_mode, &local_page_pool)?;

    // Clear the memory so no VM or device can see the previous contents.
    if !clear_memory(pa_begin, pa_end, &local_page_pool) {
        assert!(from_state
            .ptable
            .identity_map(pa_begin, pa_end, orig_from_mode, &local_page_pool)
            .is_some());

        return None;
    }

    // Complete the transfer by mapping the memory into the recipient.
    if to_state
        .ptable
        .identity_map(pa_begin, pa_end, to_mode, &local_page_pool)
        .is_none()
    {
        // TODO: partial defrag of failed range.
        // Recover any memory consumed in failed mapping.
        from_state.ptable.defrag(&local_page_pool);
        // goto fail_return_to_sender;
        assert!(from_state
            .ptable
            .identity_map(pa_begin, pa_end, orig_from_mode, &local_page_pool)
            .is_some());

        return None;
    }

    Some(())
}
#[no_mangle]
pub unsafe extern "C" fn api_share_memory(
    vm_id: spci_vm_id_t,
    addr: ipaddr_t,
    size: size_t,
    share: usize,
    current: *const VCpu,
) -> i64 {
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

    match share_memory(vm_id, addr, size, share, &*current) {
        Some(_) => 0,
        None => -1,
    }
}

/// Returns the version of the implemented SPCI specification.
#[no_mangle]
pub extern "C" fn api_spci_version() -> i32 {
    // Ensure that both major and minor revision representation occupies at
    // most 15 bits.
    const_assert!(0x8000 > SPCI_VERSION_MAJOR);
    const_assert!(0x10000 > SPCI_VERSION_MINOR);

    (SPCI_VERSION_MAJOR << SPCI_VERSION_MAJOR_OFFSET) | SPCI_VERSION_MINOR
}

#[no_mangle]
pub unsafe extern "C" fn api_debug_log(c: c_char, current: *mut VCpu) -> i64 {
    let vm = (*current).vm;
    (*vm).debug_log(c);
    0
}
