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
use core::ops::Deref;
use core::ptr;
use core::sync::atomic::Ordering;

use crate::abi::*;
use crate::addr::*;
use crate::arch::*;
use crate::cpu::*;
use crate::mm::*;
use crate::mpool::*;
use crate::page::*;
use crate::spci::*;
use crate::spci_architected_message::*;
use crate::spinlock::*;
use crate::std::*;
use crate::types::*;
use crate::utils::*;
use crate::vm::*;

pub struct Hypervisor {
    pub mpool: MPool,
    pub memory_manager: MemoryManager,
    pub cpu_manager: CpuManager,
    pub vm_manager: VmManager,
}

impl Hypervisor {
    // Creates a new hypervisor instance.
    pub fn new(
        mpool: MPool,
        memory_manager: MemoryManager,
        cpu_manager: CpuManager,
        vm_manager: VmManager,
    ) -> Self {
        Self {
            mpool,
            memory_manager,
            cpu_manager,
            vm_manager,
        }
    }

    /// Switches the physical CPU back to the corresponding vcpu of the primary VM.
    ///
    /// This triggers the scheduling logic to run. Run in the context of secondary VM to cause
    /// HF_VCPU_RUN to return and the primary VM to regain control of the cpu.
    fn switch_to_primary(
        &self,
        current: &mut VCpuExecutionLocked,
        mut primary_ret: HfVCpuRunReturn,
        secondary_state: VCpuStatus,
    ) -> &VCpu {
        let primary = self.vm_manager.get_primary();
        let next = &primary.vcpus[self.cpu_manager.index_of(current.get_inner().cpu)];

        // If the secondary is blocked but has a timer running, sleep until the timer fires rather
        // than indefinitely.
        match &mut primary_ret {
            HfVCpuRunReturn::WaitForInterrupt { ns } | HfVCpuRunReturn::WaitForMessage { ns } => {
                *ns = if unsafe { arch_timer_enabled_current() } {
                    unsafe { arch_timer_remaining_ns_current() }
                } else {
                    HF_SLEEP_INDEFINITE
                };
            }
            _ => {}
        }

        // Set the return value for the primary VM's call to HF_VCPU_RUN.
        //
        // The use of `get_mut_unchecked()` is safe because the currently running pCPU implicitly
        // owns `next`. Notice that `next` is the vCPU of the primary VM that corresponds to the
        // currently running pCPU.
        unsafe { next.inner.get_mut_unchecked() }
            .regs
            .set_retval(primary_ret.into_raw());

        // Mark the current vcpu as waiting.
        current.get_inner_mut().state = secondary_state;

        next
    }

    /// Returns to the primary vm and signals that the vcpu still has work to do so.
    pub fn preempt(&self, current: &mut VCpuExecutionLocked) -> &VCpu {
        self.switch_to_primary(current, HfVCpuRunReturn::Preempted, VCpuStatus::Ready)
    }

    /// Puts the current vcpu in wait for interrupt mode, and returns to the primary vm.
    pub fn wait_for_interrupt(&self, current: &mut VCpuExecutionLocked) -> &VCpu {
        self.switch_to_primary(
            current,
            HfVCpuRunReturn::WaitForInterrupt {
                ns: HF_SLEEP_INDEFINITE,
            },
            VCpuStatus::BlockedInterrupt,
        )
    }

    /// Puts the current vCPU in off mode, and returns to the primary VM.
    pub fn vcpu_off(&self, current: &mut VCpuExecutionLocked) -> &VCpu {
        // Disable the timer, so the scheduler doesn't get told to call back based on it.
        unsafe {
            arch_timer_disable_current();
        }

        self.switch_to_primary(
            current,
            HfVCpuRunReturn::WaitForInterrupt {
                ns: HF_SLEEP_INDEFINITE,
            },
            VCpuStatus::Off,
        )
    }

    /// Returns to the primary vm to allow this cpu to be used for other tasks as the vcpu does not
    /// have work to do at this moment. The current vcpu is masked as ready to be scheduled again.
    pub fn spci_yield(&self, current: &mut VCpuExecutionLocked) -> Option<&VCpu> {
        if unsafe { (*current.vm).id } == HF_PRIMARY_VM_ID {
            // Noop on the primary as it makes the scheduling decisions.
            return None;
        }

        Some(self.switch_to_primary(current, HfVCpuRunReturn::Yield, VCpuStatus::Ready))
    }

    /// Switches to the primary so that it can switch to the target, or kick tit if it is already
    /// running on a different physical CPU.
    pub fn wake_up(&self, current: &mut VCpuExecutionLocked, target_vcpu: &VCpu) -> &VCpu {
        self.switch_to_primary(
            current,
            HfVCpuRunReturn::WakeUp {
                vm_id: unsafe { (*target_vcpu.vm).id },
                vcpu: target_vcpu.index(),
            },
            VCpuStatus::Ready,
        )
    }

    /// Aborts the vCPU and triggers its VM to abort fully.
    pub fn abort(&self, current: &mut VCpuExecutionLocked) -> &VCpu {
        let vm = unsafe { &*current.vm };

        dlog!("Aborting VM {} vCPU {}\n", vm.id, current.index(),);

        if vm.id == HF_PRIMARY_VM_ID {
            // TODO: what to do when the primary aborts?
            spin_loop();
        }

        vm.aborting.store(true, Ordering::Relaxed);

        // TODO: free resources once all vCPUs abort.

        self.switch_to_primary(current, HfVCpuRunReturn::Aborted, VCpuStatus::Aborted)
    }

    /// Returns the ID of the VM.
    pub fn vm_get_id(&self, current: &VCpu) -> spci_vm_id_t {
        unsafe { (*current.vm).id }
    }

    /// Returns the number of VMs configured to run.
    pub fn vm_get_count(&self) -> spci_vm_count_t {
        self.vm_manager.len() as _
    }

    /// Returns the number of vCPUs configured in the given VM, or 0 if there is no such VM or the
    /// caller is not the primary VM.
    pub fn vcpu_get_count(&self, vm_id: spci_vm_id_t, current: &VCpu) -> Option<spci_vcpu_count_t> {
        // Only the primary VM needs to know about vcpus for scheduling.
        if unsafe { (*current.vm).id } != HF_PRIMARY_VM_ID {
            return None;
        }

        let vm = self.vm_manager.get(vm_id)?;

        Some(vm.vcpus.len() as _)
    }

    /// Assuming that the arguments have already been checked by the caller, injects a virtual
    /// interrupt of the given ID into the given target vCPU. This doesn't cause the vCPU to
    /// actually be run immediately; it will be taken when the vCPU is next run, which is up to the
    /// scheduler.
    ///
    /// Returns:
    ///  - 0 on success if no further action is needed.
    ///  - 1 if it was called by the primary VM and the primary VM now needs to wake up or kick the
    ///      target vCPU.
    fn internal_interrupt_inject(
        &self,
        target_vcpu: &VCpu,
        intid: intid_t,
        current: &mut VCpuExecutionLocked,
    ) -> (i64, Option<&VCpu>) {
        if target_vcpu.interrupts.lock().inject(intid).is_ok() {
            if unsafe { (*current.vm).id } == HF_PRIMARY_VM_ID {
                // If the call came from the primary VM, let it know that it should run or kick the
                // target vCPU.
                return (1, None);
            }

            if current.deref().deref() as *const _ != target_vcpu as *const _ {
                return (0, Some(self.wake_up(current, target_vcpu)));
            }
        }

        (0, None)
    }

    /// Prepares the vcpu to run by updating its state and fetching whether a return value needs to
    /// be forced onto the vCPU.
    ///
    /// Returns:
    ///  - Err if it fails to prepare `vcpu` to run.
    ///  - Ok  if it succeeds to prepare `vcpu` to run. In this case, `vcpu.execution_lock` has
    ///        acquired.
    ///
    /// TODO(HfO2): `current` is vCPU of primary VM, thus not locked actually.
    fn vcpu_prepare_run(
        &self,
        current: &VCpuExecutionLocked,
        vcpu: &VCpu,
        run_ret: HfVCpuRunReturn,
    ) -> Result<VCpuExecutionLocked, HfVCpuRunReturn> {
        let mut vcpu_inner = vcpu.inner.try_lock().map_err(|_| {
            // vCPU is running or prepared to run on another pCPU.
            //
            // It's ok not to return the sleep duration here because the other physical CPU that is
            // currently running this vCPU will return the sleep duration if needed. The default
            // return value is HfVCpuRunReturn::WaitForInterrupt, so no need to set it explicitly.
            run_ret
        })?;

        let vm = unsafe { &*vcpu.vm };

        if vm.aborting.load(Ordering::Relaxed) {
            if vcpu_inner.state != VCpuStatus::Aborted {
                dlog!("Aborting VM {} vCPU {}\n", vm.id, vcpu.index());
                vcpu_inner.state = VCpuStatus::Aborted;
            }
            return Err(run_ret);
        }

        match vcpu_inner.state {
            VCpuStatus::Off | VCpuStatus::Aborted => {
                return Err(run_ret);
            }

            // A pending message allows the vCPU to run so the message can be delivered directly.
            // The VM needs to be locked to deliver mailbox messages.
            // The VM lock is not needed in the common case so it must only be taken when it is
            // going to be needed. This ensures there are no inter-vCPU dependencies in the common
            // run case meaning the sensitive context switch performance is consistent.
            VCpuStatus::BlockedMailbox if vm.inner.lock().try_read().is_ok() => {
                vcpu_inner.regs.set_retval(SpciReturn::Success as uintreg_t);
            }

            // Allow virtual interrupts to be delivered.
            // The timer expired so allow the interrupt to be delivered.
            // The vCPU is not ready to run, return the appropriate code to the primary which
            // called vcpu_run.
            VCpuStatus::BlockedMailbox | VCpuStatus::BlockedInterrupt
                if !vcpu.interrupts.lock().is_interrupted() && !vcpu_inner.regs.timer_pending() =>
            {
                let run_ret = if !vcpu_inner.regs.timer_enabled() {
                    run_ret
                } else {
                    let ns = vcpu_inner.regs.timer_remaining_ns();
                    if vcpu_inner.state == VCpuStatus::BlockedMailbox {
                        HfVCpuRunReturn::WaitForMessage { ns }
                    } else {
                        HfVCpuRunReturn::WaitForInterrupt { ns }
                    }
                };
                return Err(run_ret);
            }

            _ => {
                // Do nothing.
            }
        }

        // It has been decided that the vCPU should be run.
        vcpu_inner.cpu = current.get_inner().cpu;

        // We want to keep the lock of vcpu.state because we're going to run.
        mem::forget(vcpu_inner);
        Ok(unsafe { VCpuExecutionLocked::from_raw(vcpu) })
    }

    /// Runs the given vcpu of the given vm.
    pub fn vcpu_run(
        &self,
        vm_id: spci_vm_id_t,
        vcpu_idx: spci_vcpu_index_t,
        current: &mut VCpuExecutionLocked,
    ) -> Result<VCpuExecutionLocked, HfVCpuRunReturn> {
        let ret = HfVCpuRunReturn::WaitForInterrupt {
            ns: HF_SLEEP_INDEFINITE,
        };

        // Only the primary VM can switch vcpus.
        if unsafe { (*current.vm).id } != HF_PRIMARY_VM_ID {
            return Err(ret);
        }

        // Only the secondary VM vcpus can be run.
        if vm_id == HF_PRIMARY_VM_ID {
            return Err(ret);
        }

        // The requested VM must exist.
        let vm = some_or!(self.vm_manager.get(vm_id), return Err(ret));

        // The requested vcpu must exist.
        let vcpu = some_or!(vm.vcpus.get(vcpu_idx as usize), return Err(ret));

        // Update state if allowed.
        let mut vcpu_locked = self.vcpu_prepare_run(current, vcpu, ret)?;

        // Inject timer interrupt if timer has expired. It's safe to access vcpu->regs here because
        // vcpu_prepare_run already made sure that regs_available was true (and then set it to
        // false) before returning true.
        if vcpu_locked.get_inner().regs.timer_pending() {
            // Make virtual timer interrupt pending.
            self.internal_interrupt_inject(&*vcpu, HF_VIRTUAL_TIMER_INTID, &mut vcpu_locked);

            // Set the mask bit so the hardware interrupt doesn't fire again. Ideally we wouldn't
            // do this because it affects what the secondary vcPU sees, but if we don't then we end
            // up with a loop of the interrupt firing each time we try to return to the secondary
            // vCPU.
            vcpu_locked.get_inner_mut().regs.timer_mask();
        }

        // Switch to the vcpu.
        Ok(vcpu_locked)
    }

    /// Determines the value to be returned by api_vm_configure and api_mailbox_clear after they've
    /// succeeded. If a secondary VM is running and there are waiters, it also switches back to the
    /// primary VM for it to wake waiters up.
    fn waiter_result(
        &self,
        vm_id: spci_vm_id_t,
        vm_inner: &VmInner,
        current: &mut VCpuExecutionLocked,
    ) -> (i64, Option<&VCpu>) {
        if vm_inner.is_waiter_list_empty() {
            // No waiters, nothing else to do.
            return (0, None);
        }

        if vm_id == HF_PRIMARY_VM_ID {
            // The caller is the primary VM. Tell it to wake up waiters.
            return (1, None);
        }

        // Switch back to the primary VM, informing it that there are waiters that need to be
        // notified.
        let next =
            self.switch_to_primary(current, HfVCpuRunReturn::NotifyWaiters, VCpuStatus::Ready);

        (0, Some(next))
    }

    /// Configures the VM to send/receive data through the specified pages. The pages must not be
    /// shared.
    ///
    /// Returns:
    ///  - -1 on failure.
    ///  - 0 on success if no further action is needed.
    ///  - 1 if it was called by the primary VM and the primary VM now needs to wake up or kick
    ///    waiters. Waiters should be retrieved by calling hf_mailbox_waiter_get.
    pub fn vm_configure(
        &self,
        send: ipaddr_t,
        recv: ipaddr_t,
        current: &mut VCpuExecutionLocked,
    ) -> (i64, Option<&VCpu>) {
        let vm = unsafe { &*current.vm };

        // The hypervisor's memory map must be locked for the duration of this operation to ensure
        // there will be sufficient memory to recover from any failures.
        //
        // TODO: the scope of the can be reduced but will require restructing to keep a single
        //       unlock point.
        let mut vm_inner = vm.inner.lock();
        if vm_inner
            .configure(
                send,
                recv,
                &self.memory_manager.hypervisor_ptable,
                &self.mpool,
            )
            .is_err()
        {
            return (-1, None);
        }

        // Tell caller about waiters, if any.
        self.waiter_result(vm.id, &vm_inner, current)
    }

    /// Copies data from the sender's send buffer to the recipient's receive buffer and notifies
    /// the recipient.
    ///
    /// If the recipient's receive buffer is busy, it can optionally register the caller to be
    /// notified when the recipient's receive buffer becomes available.
    pub fn spci_msg_send(
        &self,
        attributes: SpciMsgSendAttributes,
        current: &mut VCpuExecutionLocked,
    ) -> (SpciReturn, Option<&VCpu>) {
        let from = unsafe { &*current.vm };

        let notify = attributes.contains(SpciMsgSendAttributes::NOTIFY);

        // Check that the sender has configured its send buffer. If the tx mailbox at from_msg is
        // configured (i.e. from_msg != ptr::null()) then it can be safely accessed after releasing
        // the lock since the tx mailbox address can only be configured once.
        let from_msg = some_or!(
            unsafe { from.inner.lock().get_send_ptr().as_ref() },
            return (SpciReturn::InvalidParameters, None)
        );

        // Copy the message header.
        // Note that the payload is not copied when the message header is.
        let from_msg_replica = unsafe { ptr::read(from_msg) };
        let from_msg_payload_length = from_msg_replica.length as usize;

        // Ensure source VM id corresponds to the current VM.
        if from_msg_replica.source_vm_id != from.id {
            return (SpciReturn::InvalidParameters, None);
        }

        // Limit the size of transfer.
        if from_msg_payload_length > SPCI_MSG_PAYLOAD_MAX {
            return (SpciReturn::InvalidParameters, None);
        }

        // Disallow reflexive requests as this suggests an error in the VM.
        if from_msg_replica.target_vm_id == from.id {
            return (SpciReturn::InvalidParameters, None);
        }

        // Ensure the target VM exists.
        let to = some_or!(
            self.vm_manager.get(from_msg_replica.target_vm_id),
            return (SpciReturn::InvalidParameters, None)
        );

        // Hf needs to hold the lock on `to` before the mailbox state is checked. The lock on `to`
        // must be held until the information is copied to `to` Rx buffer. Since in
        // spci_msg_handle_architected_message we may call api_spci_share_memory which must hold
        // the `from` lock, we must hold the `from` lock at this point to prevent a deadlock
        // scenario.
        let (mut to_inner, mut from_inner) = SpinLock::lock_both(&to.inner, &from.inner);

        if !to_inner.is_empty() || !to_inner.is_configured() {
            // Fail if the target isn't currently ready to receive data, setting up for
            // notification if requested.
            if notify {
                let _ = from_inner.wait_for(&mut to_inner, to.id);
            }

            return (SpciReturn::Busy, None);
        }

        let to_msg = unsafe { &mut *to_inner.get_recv_ptr() };

        // Handle architected messages.
        if from_msg_replica.flags.contains(SpciMessageFlags::IMPDEF) {
            *to_msg = from_msg_replica;
            unsafe {
                ptr::copy_nonoverlapping(
                    from_msg.payload.as_ptr(),
                    to_msg.payload.as_mut_ptr(),
                    from_msg_payload_length,
                );
            }
        } else {
            // Buffer holding the internal copy of the shared memory regions.
            // TODO: Buffer is temporarily in the stack.
            let mut message_buffer: [u8; mem::size_of::<SpciArchitectedMessageHeader>()
                + mem::size_of::<SpciMemoryRegionConstituent>()
                + mem::size_of::<SpciMemoryRegion>()] =
                unsafe { MaybeUninit::uninit().assume_init() };

            let architected_header = from_msg.get_architected_message_header();

            if from_msg_payload_length > message_buffer.len() {
                return (SpciReturn::InvalidParameters, None);
            }

            if from_msg_payload_length < mem::size_of::<SpciArchitectedMessageHeader>() {
                return (SpciReturn::InvalidParameters, None);
            }

            // Copy the architected message into an internal buffer.
            unsafe {
                ptr::copy_nonoverlapping(
                    architected_header as *const _ as _,
                    message_buffer.as_mut_ptr(),
                    from_msg_payload_length,
                );
            }

            #[allow(clippy::cast_ptr_alignment)]
            let architected_message_replica =
                unsafe { &*(message_buffer.as_ptr() as *const SpciArchitectedMessageHeader) };

            // Note that message_buffer is passed as the third parameter to
            // spci_msg_handle_architected_message. The execution flow commencing at
            // spci_msg_handle_architected_message will make several accesses to fields in
            // message_buffer. The memory area message_buffer must be exclusively owned by Hf so
            // that TOCTOU issues do not arise.
            let ret = spci_msg_handle_architected_message(
                &mut to_inner,
                &mut from_inner,
                architected_message_replica,
                &from_msg_replica,
                to_msg,
                &self.mpool,
            );

            if ret != SpciReturn::Success {
                return (ret, None);
            }
        }

        let primary_ret = HfVCpuRunReturn::Message { vm_id: to.id };

        // Messages for the primary VM are delivered directly.
        if to.id == HF_PRIMARY_VM_ID {
            to_inner.set_read();
            let next = self.switch_to_primary(current, primary_ret, VCpuStatus::Ready);
            return (SpciReturn::Success, Some(next));
        }

        to_inner.set_received();

        // Return to the primary VM directly or with a switch.
        let next = if from.id != HF_PRIMARY_VM_ID {
            Some(self.switch_to_primary(current, primary_ret, VCpuStatus::Ready))
        } else {
            None
        };

        (SpciReturn::Success, next)
    }

    /// Receives a message from the mailbox. If one isn't available, this function can optionally
    /// block the caller until one becomes available.
    ///
    /// No new messages can be received until the mailbox has been cleared.
    pub fn spci_msg_recv(
        &self,
        attributes: SpciMsgRecvAttributes,
        current: &mut VCpuExecutionLocked,
    ) -> (SpciReturn, Option<&VCpu>) {
        let vm = unsafe { &*current.vm };
        let block = attributes.contains(SpciMsgRecvAttributes::BLOCK);

        // The primary VM will receive messages as a status code from running vcpus and must not
        // call this function.
        if vm.id == HF_PRIMARY_VM_ID {
            return (SpciReturn::Interrupted, None);
        }

        let mut vm_inner = vm.inner.lock();

        // Return pending messages without blocking.
        if vm_inner.try_read().is_ok() {
            return (SpciReturn::Success, None);
        }

        // No pending message so fail if not allowed to block.
        if !block {
            return (SpciReturn::Retry, None);
        }

        // From this point onward this call can only be interrupted or a message received. If a
        // message is received the return value will be set at that time to SPCI_SUCCESS.
        //
        // Block only if there are enabled and pending interrupts, to match behaviour of
        // wait_for_interrupt.
        let next = if !current.interrupts.lock().is_interrupted() {
            // Switch back to primary vm to block.
            Some(self.switch_to_primary(
                current,
                HfVCpuRunReturn::WaitForMessage {
                    ns: HF_SLEEP_INDEFINITE,
                },
                VCpuStatus::BlockedMailbox,
            ))
        } else {
            None
        };

        (SpciReturn::Interrupted, next)
    }

    /// Retrieves the next VM whose mailbox became writable. For a VM to be notified by this
    /// function, the caller must have called api_mailbox_send before with the notify argument set
    /// to true, and this call must have failed because the mailbox was not available.
    ///
    /// It should be called repeatedly to retrieve a list of VMs.
    pub fn mailbox_writable_get(&self, current: &VCpu) -> Option<spci_vm_id_t> {
        let vm = unsafe { &*current.vm };
        vm.inner.lock().dequeue_ready_list()
    }

    /// Retrieves the next VM waiting to be notified that the mailbox of the specified VM became
    /// writable. Only primary VMs are allowed to call this.
    pub fn mailbox_waiter_get(&self, vm_id: spci_vm_id_t, current: &VCpu) -> Option<spci_vm_id_t> {
        // Only primary VMs are allowed to call this function.
        if unsafe { (*current.vm).id } != HF_PRIMARY_VM_ID {
            return None;
        }

        let vm = self.vm_manager.get(vm_id)?;

        // Check if there are outstanding notifications from given vm.
        let entry = unsafe { vm.inner.lock().fetch_waiter().as_mut()? };

        // Enqueue notification to waiting VM.
        let waiting_vm = unsafe { &*entry.waiting_vm };

        let mut vm_inner = waiting_vm.inner.lock();
        if !entry.is_in_ready_list() {
            vm_inner.enqueue_ready_list(&mut *entry);
        }

        Some(waiting_vm.id)
    }

    /// Clears the caller's mailbox so that a new message can be received. The caller must have
    /// copied out all data they wish to preserve as new messages will overwrite the old and will
    /// arrive asynchronously.
    ///
    /// Returns:
    ///  - -1 on failure, if the mailbox hasn't been read.
    ///  - 0 on success if no further action is needed.
    ///  - 1 if it was called by the primary VM and the primary VM now needs to wake
    ///    up or kick waiters. Waiters should be retrieved by calling
    ///    hf_mailbox_waiter_get.
    pub fn mailbox_clear(&self, current: &mut VCpuExecutionLocked) -> (i64, Option<&VCpu>) {
        let vm = unsafe { &*current.vm };
        let mut vm_inner = vm.inner.lock();
        match vm_inner.get_state() {
            MailboxState::Empty => (0, None),
            MailboxState::Received => (-1, None),
            MailboxState::Read => {
                vm_inner.set_empty();
                self.waiter_result(vm.id, &vm_inner, current)
            }
        }
    }

    /// Enables or disables a given interrupt ID for the calling vCPU.
    ///
    /// Fails if the intid is invalid.
    pub fn interrupt_enable(&self, intid: intid_t, enable: bool, current: &VCpu) -> Result<(), ()> {
        current.interrupts.lock().enable(intid, enable)
    }

    /// Returns the ID of the next pending interrupt for the calling vCPU, and acknowledges it
    /// (i.e. marks it as no longer pending). Returns HF_INVALID_INTID if there are no pending
    /// interrupts.
    pub fn interrupt_get(&self, current: &VCpu) -> intid_t {
        current.interrupts.lock().get()
    }

    /// Returns whether the current vCPU is allowed to inject an interrupt into the given VM and
    /// vCPU.
    #[inline]
    fn is_injection_allowed(&self, target_vm_id: spci_vm_id_t, current: &VCpu) -> bool {
        let current_vm_id = unsafe { (*current.vm).id };

        // The primary VM is allowed to inject interrupts into any VM. Secondary
        // VMs are only allowed to inject interrupts into their own vCPUs.
        current_vm_id == HF_PRIMARY_VM_ID || current_vm_id == target_vm_id
    }

    /// Injects a virtual interrupt of the given ID into the given target vCPU. This doesn't cause
    /// the vCPU to actually be run immediately; it will be taken when the vCPU is next run, which
    /// is up to the scheduler.
    ///
    /// Returns:
    ///  - -1 on failure because the target VM or vCPU doesn't exist, the interrupt ID is invalid,
    ///       or the current VM is not allowed to inject interrupts to the target VM.
    ///  - 0  on success if no further action is needed.
    ///  - 1  if it was called by the primary VM and the primary VM now needs to wake up or kick
    ///       the target vCPU.
    pub fn interrupt_inject(
        &self,
        target_vm_id: spci_vm_id_t,
        target_vcpu_idx: spci_vcpu_index_t,
        intid: intid_t,
        current: &mut VCpuExecutionLocked,
    ) -> (i64, Option<&VCpu>) {
        let target_vm = some_or!(self.vm_manager.get(target_vm_id), return (-1, None));

        if intid >= HF_NUM_INTIDS {
            return (-1, None);
        }

        if !self.is_injection_allowed(target_vm_id, current.deref()) {
            return (-1, None);
        }

        let target_vcpu = some_or!(
            target_vm.vcpus.get(target_vcpu_idx as usize),
            return (-1, None)
        );

        dlog!(
            "Injecting IRQ {} for VM {} VCPU {} from VM {} VCPU {}\n",
            intid,
            target_vm_id,
            target_vcpu_idx,
            unsafe { &*current.vm }.id,
            unsafe { &*current.get_inner().cpu }.id
        );

        self.internal_interrupt_inject(target_vcpu, intid, current)
    }

    /// Clears a region of physical memory by overwriting it with zeros. The data is flushed from
    /// the cache so the memory has been cleared across the system.
    fn clear_memory(&self, begin: paddr_t, end: paddr_t, ppool: &MPool) -> Result<(), ()> {
        let mut hypervisor_ptable = self.memory_manager.hypervisor_ptable.lock();
        let size = pa_difference(begin, end);
        let region = pa_addr(begin);

        // TODO: change this to a cpu local single page window rather than a global mapping of the
        //       whole range. Such an approach will limit the changes to stage-1 tables and will
        //       allow only local invalidation.

        if hypervisor_ptable
            .identity_map(begin, end, Mode::W, ppool)
            .is_err()
        {
            // TODO: partial defrag of failed range.
            // Recover any memory consumed in failed mapping.
            hypervisor_ptable.defrag(ppool);
            return Err(());
        }

        unsafe {
            ptr::write_bytes(region as *mut u8, 0, size);
            arch_mm_write_back_dcache(region as usize, size);
        }

        hypervisor_ptable.unmap(begin, end, ppool).unwrap();
        Ok(())
    }

    /// Shares memory from the calling VM with another. The memory can be shared in different modes.
    ///
    /// TODO: the interface for sharing memory will need to be enhanced to allow sharing with
    ///       different modes e.g. read-only, informing the recipient of the memory they have been
    ///       given, opting to not wipe the memory and possibly allowing multiple blocks to be
    ///       transferred. What this will look like is TBD.
    pub fn share_memory(
        &self,
        vm_id: spci_vm_id_t,
        addr: ipaddr_t,
        size: usize,
        share: HfShare,
        current: &VCpu,
    ) -> Result<(), ()> {
        let from: &Vm = unsafe { &*current.vm };

        // Disallow reflexive shares as this suggests an error in the VM.
        if vm_id == from.id {
            return Err(());
        }

        // Ensure the target VM exists.
        let to = self.vm_manager.get(vm_id).ok_or(())?;

        let begin = addr;
        let end = ipa_add(addr, size);

        // Fail if addresses are not page-aligned.
        if !is_aligned(ipa_addr(begin), PAGE_SIZE) || !is_aligned(ipa_addr(end), PAGE_SIZE) {
            return Err(());
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

        // Create a local pool so any freed memory can't be used by another thread. This is to
        // ensure the original mapping can be restored if any stage of the process fails.
        let local_page_pool = MPool::new_with_fallback(&self.mpool);

        let (mut from_inner, mut to_inner) = SpinLock::lock_both(&from.inner, &to.inner);

        // Ensure that the memory range is mapped with the same mode so that changes can be
        // reverted if the process fails.
        // Also ensure the memory range is valid for the sender. If it isn't, the sender has either
        // shared it with another VM already or has no claim to the memory.
        let orig_from_mode = from_inner.ptable.get_mode(begin, end)?;

        if orig_from_mode.contains(Mode::INVALID) {
            return Err(());
        }

        // The sender must own the memory and have exclusive access to it in order to share it.
        // Alternatively, it is giving memory back to the owning VM.
        if orig_from_mode.contains(Mode::UNOWNED) {
            let to_mode = to_inner.ptable.get_mode(begin, end)?;

            if to_mode.contains(Mode::UNOWNED) {
                return Err(());
            }

            if share != HfShare::Give {
                return Err(());
            }
        } else if orig_from_mode.contains(Mode::SHARED) {
            return Err(());
        }

        let pa_begin = pa_from_ipa(begin);
        let pa_end = pa_from_ipa(end);

        // First update the mapping for the sender so there is not overlap with the recipient.
        from_inner
            .ptable
            .identity_map(pa_begin, pa_end, from_mode, &local_page_pool)?;

        // Clear the memory so no VM or device can see the previous contents.
        if self
            .clear_memory(pa_begin, pa_end, &local_page_pool)
            .is_err()
        {
            from_inner
                .ptable
                .identity_map(pa_begin, pa_end, orig_from_mode, &local_page_pool)
                .unwrap();

            return Err(());
        }

        // Complete the transfer by mapping the memory into the recipient.
        if to_inner
            .ptable
            .identity_map(pa_begin, pa_end, to_mode, &local_page_pool)
            .is_err()
        {
            // TODO: partial defrag of failed range.
            // Recover any memory consumed in failed mapping.
            from_inner.ptable.defrag(&local_page_pool);
            from_inner
                .ptable
                .identity_map(pa_begin, pa_end, orig_from_mode, &local_page_pool)
                .unwrap();

            return Err(());
        }

        Ok(())
    }

    /// Returns the version of the implemented SPCI specification.
    pub fn spci_version(&self) -> i32 {
        // Ensure that both major and minor revision representation occupies at most 15 bits.
        const_assert!(0x8000 > SPCI_VERSION_MAJOR);
        const_assert!(0x10000 > SPCI_VERSION_MINOR);

        (SPCI_VERSION_MAJOR << SPCI_VERSION_MAJOR_OFFSET) | SPCI_VERSION_MINOR
    }

    pub fn debug_log(&self, c: c_char, current: &VCpu) {
        let vm = unsafe { &*current.vm };
        vm.debug_log(c);
    }
}
