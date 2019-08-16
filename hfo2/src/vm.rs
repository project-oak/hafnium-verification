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

use core::mem;
use core::mem::MaybeUninit;
use core::ptr;
use core::sync::atomic::AtomicBool;

use arrayvec::ArrayVec;

use crate::arch::*;
use crate::cpu::*;
use crate::list::*;
use crate::mm::*;
use crate::mpool::*;
use crate::spci::*;
use crate::spinlock::*;
use crate::std::*;
use crate::types::*;
use crate::dlog::*;
use crate::addr::*;
use crate::page::*;

const LOG_BUFFER_SIZE: usize = 256;

#[repr(C)]
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum MailboxState {
    /// There is no message in the mailbox.
    Empty,

    /// There is a message in the mailbox that is waiting for a reader.
    Received,

    /// There is a message in the mailbox that has been read.
    Read,
}

#[repr(C)]
pub struct WaitEntry {
    /// The VM that is waiting for a mailbox to become writable.
    pub waiting_vm: *const Vm,

    /// Links used to add entry to a VM's waiter_list. This is protected by the notifying VM's lock.
    pub wait_links: list_entry,

    /// Links used to add entry to a VM's ready_list. This is protected by the waiting VM's lock.
    pub ready_links: list_entry,
}

#[repr(C)]
pub struct Mailbox {
    state: MailboxState,

    // Addresses to page used for receiving and sending messages.
    // Those pages are not protected by lock -- sender and receiver should
    // have a proper protocol so that Hafnium copies synchronized data.
    recv: *mut SpciMessage,
    send: *const SpciMessage,

    /// List of wait_entry structs representing VMs that want to be notified
    /// when the mailbox becomes writable. Once the mailbox does become
    /// writable, the entry is removed from this list and added to the waiting
    /// VM's ready_list.
    waiter_list: list_entry,

    /// List of wait_entry structs representing VMs whose mailboxes became
    /// writable since the owner of the mailbox registers for notification.
    ready_list: list_entry,
}

impl Mailbox {
    /// Initializes the mailbox.
    /// TODO: Refactor `vm_init` and make `Mailbox::new()` instead of this.
    pub unsafe fn init(&mut self) {
        list_init(&mut self.waiter_list);
        list_init(&mut self.ready_list);

        self.state = MailboxState::Empty;
    }

    /// Retrieves the next waiter and removes it from the wait list if the VM's
    /// mailbox is in a writable state.
    pub unsafe fn fetch_waiter(&mut self) -> *mut WaitEntry {
        let entry: *mut WaitEntry;

        if self.state != MailboxState::Empty
            || self.recv == ptr::null_mut()
            || list_empty(&self.waiter_list)
        {
            // The mailbox is not writable or there are no waiters.
            return ptr::null_mut();
        }

        // Remove waiter from the wait list.
        entry = container_of!(self.waiter_list.next, WaitEntry, wait_links);
        list_remove(&mut (*entry).wait_links);
        entry
    }

    /// Checks if any waiters exists.
    pub fn any_waiter(&self) -> bool {
        unsafe { list_empty(&self.waiter_list) }
    }

    /// Checks whether there exists a pending message. If one exists, marks the
    /// mailbox read.
    pub fn try_read(&mut self) -> bool {
        if self.state == MailboxState::Received {
            self.state = MailboxState::Read;
            true
        } else {
            false
        }
    }

    /// Set the arrived message is read.
    pub fn set_read(&mut self) {
        self.state = MailboxState::Read;
    }

    /// Set a message is arrived.
    pub fn set_received(&mut self) {
        self.state = MailboxState::Received;
    }

    /// Configures the hypervisor's stage-1 view of the send and receive pages.
    /// The stage-1 page tables must be locked so memory cannot be taken by 
    /// another core which could result in this transaction being unable to 
    /// roll back in the case of an error.
    pub fn configure_stage1(
        &mut self,
        pa_send_begin: paddr_t,
        pa_send_end: paddr_t,
        pa_recv_begin: paddr_t,
        pa_recv_end: paddr_t,
        local_page_pool: &mut MPool,
    ) -> Option<()> {
        let mut hypervisor_ptable = lock_hypervisor_ptable();

        // Map the send page as read-only in the hypervisor address space.
        if let Some(_) = hypervisor_ptable.identity_map(
            pa_send_begin,
            pa_send_end,
            Mode::R,
            local_page_pool,
        ) {
            self.send = pa_addr(pa_send_begin) as usize as *const SpciMessage;
        } else {
            // TODO: partial defrag of failed range.
            // Recover any memory consumed in failed mapping.
            hypervisor_ptable.defrag(local_page_pool);
            return None;
        }

        // Map the receive page as writable in the hypervisor address space. On
        // failure, unmap the send page before returning.
        if let Some(_) = hypervisor_ptable.identity_map(
            pa_recv_begin,
            pa_recv_end,
            Mode::W,
            local_page_pool,
        ) {
            self.recv = pa_addr(pa_recv_begin) as usize as *mut SpciMessage;
        } else {
            // TODO: parital defrag of failed range.
            // Recover any memory consumed in failed mapping.
            hypervisor_ptable.defrag(local_page_pool);
            self.send = ptr::null();
            assert!(hypervisor_ptable.unmap(
                pa_send_begin,
                pa_send_end,
                local_page_pool
            ).is_some());

            return None;
        }

        Some(())
    }

    pub fn get_send_ptr(&self) -> *const SpciMessage {
        self.send
    }

    pub fn get_recv_ptr(&self) -> *mut SpciMessage {
        self.recv
    }
}

pub struct VmState {
    log_buffer: ArrayVec<[c_char; LOG_BUFFER_SIZE]>,
    pub ptable: PageTable<Stage2>,
    mailbox: Mailbox,

    /// Wait entries to be used when waiting on other VM mailboxes.
    wait_entries: [WaitEntry; MAX_VMS],
    arch: ArchVm,
}

impl VmState {
    /// Initializes VmState.
    pub unsafe fn init(&mut self, vm: *mut Vm, ppool: &mut MPool) -> Option<()> {
        self.mailbox.init();

        if !mm_vm_init(&mut self.ptable, ppool) {
            return None;
        }

        // Initialise waiter entries.
        for i in 0..MAX_VMS {
            self.wait_entries[i].waiting_vm = vm;
            list_init(&mut self.wait_entries[i].wait_links);
            list_init(&mut self.wait_entries[i].ready_links);
        }
        
        Some(())
    }
    
    /// Retrieves the next waiter and removes it from the wait list if the VM's
    /// mailbox is in a writable state.
    pub unsafe fn fetch_waiter(&mut self) -> *mut WaitEntry {
        self.mailbox.fetch_waiter()
    }

    /// Checks if any waiters exists.
    pub fn any_waiter(&self) -> bool {
        self.mailbox.any_waiter()
    }

    /// Checks whether there exists a pending message. If one exists, marks the
    /// mailbox read.
    pub fn try_read(&mut self) -> bool {
        self.mailbox.try_read()
    }

    /// Sets the arrived message is read.
    pub fn set_read(&mut self) {
        self.mailbox.set_read()
    }

    /// Sets a message is arrived.
    pub fn set_received(&mut self) {
        self.mailbox.set_received()
    }

    /// Configures the send and receive pages in the VM stage-2 and hypervisor
    /// stage-1 page tables. Locking of the page tables combined with a local 
    /// memory pool ensures there will always be enough memory to recover from 
    /// any errors that arise.
    fn configure_pages(
        &mut self,
        pa_send_begin: paddr_t,
        pa_send_end: paddr_t,
        orig_send_mode: Mode,
        pa_recv_begin: paddr_t,
        pa_recv_end: paddr_t,
        orig_recv_mode: Mode,
        fallback_mpool: &MPool,
    ) -> Option<()> {

        // Create a local pool so any freed memory can't be used by another
        // thread. This is to ensure the original mapping can be restored if 
        // any stage of the process fails.
        let mut local_page_pool: MPool = MPool::new_with_fallback(fallback_mpool);

        // Take memory ownership away from the VM and mark as shared.
        self.ptable.identity_map(
            pa_send_begin,
            pa_send_end,
            Mode::UNOWNED | Mode::SHARED | Mode::R | Mode::W,
            &mut local_page_pool,
        )?;

        if let None = self.ptable.identity_map(
            pa_recv_begin,
            pa_recv_end,
            Mode::UNOWNED | Mode::SHARED | Mode::R,
            &mut local_page_pool,
        ) {
            // TODO: partial defrag of failed range.
            // Recover any memory consumed in failed mapping.
            self.ptable.defrag(&local_page_pool);

            assert!(self.ptable.identity_map(
                pa_send_begin,
                pa_send_end,
                orig_send_mode,
                &mut local_page_pool
            ).is_some());
            return None;
        }

        if let None = self.mailbox.configure_stage1(
            pa_send_begin,
            pa_send_end,
            pa_recv_begin,
            pa_recv_end,
            &mut local_page_pool,
        ) {
            // goto fail_undo_send_and_recv;
            assert!(self.ptable.identity_map(
                pa_recv_begin,
                pa_recv_end,
                orig_recv_mode,
                &mut local_page_pool
            ).is_some());

            assert!(self.ptable.identity_map(
                pa_send_begin,
                pa_send_end,
                orig_send_mode,
                &mut local_page_pool
            ).is_some());

            return None;
        }

        Some(())
    }

    /// Configures the VM to send/receive data through the specified pages. The
    /// pages must not be shared.
    ///
    /// Returns:
    ///  - -1 on failure.
    ///  - 0 on success if no further action is needed.
    ///  - 1 if it was called by the primary VM and the primary VM now needs to 
    ///    wake up or kick waiters. Waiters should be retrieved by calling
    ///    hf_mailbox_waiter_get.
    pub fn configure(
        &mut self,
        send: ipaddr_t,
        recv: ipaddr_t,
        fallback_mpool: &MPool,
    ) -> Option<()> {

        // Fail if addresses are not page-aligned.
        if !is_aligned(ipa_addr(send), PAGE_SIZE) || !is_aligned(ipa_addr(recv), PAGE_SIZE) {
            return None;
        }

        // Convert to physical addresses.
        let pa_send_begin = pa_from_ipa(send);
        let pa_send_end = pa_add(pa_send_begin, PAGE_SIZE);

        let pa_recv_begin = pa_from_ipa(recv);
        let pa_recv_end = pa_add(pa_recv_begin, PAGE_SIZE);

        // Fail if the same page is used for the send and receive pages.
        if pa_addr(pa_send_begin) == pa_addr(pa_recv_begin) {
            return None;
        }

        // We only allow these to be setup once.
        if self.is_configured() {
            return None;
        }

        // Ensure the pages are valid, owned and exclusive to the VM and that 
        // the VM has the required access to the memory.
        let orig_send_mode = self.ptable.get_mode(send, ipa_add(send, PAGE_SIZE))?;

        if !orig_send_mode.valid_owned_and_exclusive()
            || !orig_send_mode.contains(Mode::R)
            || !orig_send_mode.contains(Mode::W)
        {
            return None;
        }

        let orig_recv_mode = self.ptable.get_mode(
            recv,
            ipa_add(recv, PAGE_SIZE),
        )?;
        if !orig_recv_mode.valid_owned_and_exclusive()
            || !orig_recv_mode.contains(Mode::R)
        {
            return None;
        }

        self.configure_pages(
            pa_send_begin,
            pa_send_end,
            orig_send_mode,
            pa_recv_begin,
            pa_recv_end,
            orig_recv_mode,
            fallback_mpool,
        )
    }

    /// Checks whether `configure` is called before.
    pub fn is_configured(&self) -> bool {
        !self.mailbox.send.is_null() && !self.mailbox.recv.is_null()
    }

    /// Checks whether mailbox is empty.
    pub fn is_empty(&self) -> bool {
        self.mailbox.state == MailboxState::Empty
    }

    pub fn dequeue_ready_list(&mut self) -> Option<spci_vm_id_t> {
        unsafe {
            if list_empty(&self.mailbox.ready_list) {
                return None;
            }

            let ret = {
                let entry: *mut WaitEntry =
                    container_of!(self.mailbox.ready_list.next, WaitEntry, ready_links);
                list_remove(&mut (*entry).ready_links);
                entry.offset_from(self.wait_entries.as_ptr()) as spci_vm_id_t
            };

            Some(ret)
        }
    }

    pub fn enqueue_ready_list(&mut self, entry: &mut WaitEntry) {
        debug_assert!(unsafe { list_empty(&entry.ready_links) });

        unsafe {
            list_append(&mut self.mailbox.ready_list, &mut entry.ready_links);
        }
    }

    pub fn get_state(&self) -> MailboxState {
        self.mailbox.state
    }

    pub fn set_empty(&mut self) {
        debug_assert_eq!(self.mailbox.state, MailboxState::Read);
        self.mailbox.state = MailboxState::Empty;
    }

    /// Adds `self` into the waiter list of `target`, if `self` is not waiting 
    /// for another now. Returns false if `self` is waiting for another.
    /// TODO: better name?
    pub fn wait(&mut self, target: &mut Self, target_id: spci_vm_id_t) -> bool {
        let entry = &mut self.wait_entries[target_id as usize];

        // Append waiter only if it's not there yet.
        if unsafe { list_empty(&(*entry).wait_links) } {
            unsafe {
                list_append(&mut target.mailbox.waiter_list, &mut (*entry).wait_links);
            }
            true
        } else {
            false
        }
    }

    pub fn get_send_ptr(&self) -> *const SpciMessage {
        self.mailbox.get_send_ptr()
    }

    pub fn get_recv_ptr(&self) -> *mut SpciMessage {
        self.mailbox.get_recv_ptr()
    }

    pub fn debug_log(&mut self, id: spci_vm_id_t, c: c_char) {
        if c == '\n' as u32 as u8
            || c == '\0' as u32 as u8
            || self.log_buffer.is_full()
        {
            dlog_flush_vm_buffer(id, &mut self.log_buffer);
            self.log_buffer.clear();
        } else {
            self.log_buffer.push(c);
        }
    }
}

pub struct Vm {
    pub id: spci_vm_id_t,
    pub vcpu_count: spci_vcpu_count_t,

    /// VCpus of this vm.
    /// Note: This field is regarded as a kind of mutable states of Vm, but is
    /// not contained in VmState, because
    ///   1. Mutable inner fields are contained in VCpuState.
    ///   2. VCpuState has higher lock order than one of Vm. It is nonsense to
    ///      lock VmState to acquire VCpuState.
    pub vcpus: [VCpu; MAX_CPUS],

    /// See api.c for the partial ordering on locks.
    pub state: SpinLock<VmState>,
    pub aborting: AtomicBool,
}

impl Vm {
    pub fn debug_log(&self, c: c_char) {
        self.state.lock().debug_log(self.id, c)
    }
}

/// Encapsulates a VM whose lock is held.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct VmLocked {
    pub vm: *mut Vm,
}

/// Container for two vm_locked structures.
pub struct TwoVmLocked {
    pub vm1: VmLocked,
    pub vm2: VmLocked,
}

static mut vms: MaybeUninit<[Vm; MAX_VMS]> = MaybeUninit::uninit();
static mut vm_count: spci_vm_count_t = 0;

#[no_mangle]
pub unsafe extern "C" fn vm_init(
    vcpu_count: spci_vcpu_count_t,
    ppool: *mut MPool,
    new_vm: *mut *mut Vm,
) -> bool {
    let i: i32;
    let vm: *mut Vm;

    if vm_count as usize >= MAX_VMS {
        return false;
    }

    vm = &mut vms.get_mut()[vm_count as usize];

    memset_s(
        vm as usize as _,
        mem::size_of::<Vm>(),
        0,
        mem::size_of::<Vm>(),
    );


    (*vm).id = vm_count;
    (*vm).vcpu_count = vcpu_count;
    (*vm).aborting = AtomicBool::new(false);
    (*vm).state.get_mut_unchecked().init(vm, &mut *ppool);

    // Do basic initialization of vcpus.
    for i in 0..vcpu_count {
        vcpu_init(vm_get_vcpu(vm, i), vm);
    }

    vm_count += 1;
    *new_vm = vm;

    true
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_count() -> spci_vm_count_t {
    vm_count
}

#[no_mangle]
pub unsafe extern "C" fn vm_find(id: spci_vm_id_t) -> *mut Vm {
    // Ensure the VM is initialized.
    if id >= vm_count {
        return ptr::null_mut();
    }

    &mut vms.get_mut()[id as usize]
}

/// Locks the given VM and updates `locked` to hold the newly locked vm.
#[no_mangle]
pub unsafe extern "C" fn vm_lock(vm: *mut Vm) -> VmLocked {
    let locked = VmLocked { vm };

    (*vm).state.lock().into_raw();

    locked
}

/// Locks two VMs ensuring that the locking order is according to the locks'
/// addresses.
#[no_mangle]
pub unsafe extern "C" fn vm_lock_both(vm1: *mut Vm, vm2: *mut Vm) -> TwoVmLocked {
    let dual_lock = TwoVmLocked {
        vm1: VmLocked { vm: vm1 },
        vm2: VmLocked { vm: vm2 },
    };

    SpinLock::lock_both(&(*vm1).state, &(*vm2).state);

    dual_lock
}

/// Unlocks a VM previously locked with vm_lock, and updates `locked` to reflect
/// the fact that the VM is no longer locked.
#[no_mangle]
pub unsafe extern "C" fn vm_unlock(locked: *mut VmLocked) {
    let guard: SpinLockGuard<'static, VmState> = SpinLockGuard::from_raw(&(*(*locked).vm).state as *const _ as usize);
    mem::drop(guard);
    (*locked).vm = ptr::null_mut();
}

/// Get the vCPU with the given index from the given VM.
/// This assumes the index is valid, i.e. less than vm->vcpu_count.
#[no_mangle]
pub unsafe extern "C" fn vm_get_vcpu(vm: *mut Vm, vcpu_index: spci_vcpu_index_t) -> *mut VCpu {
    assert!(vcpu_index < (*vm).vcpu_count);
    &mut (*vm).vcpus[vcpu_index as usize]
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_id(vm: *const Vm) -> spci_vm_id_t {
    (*vm).id
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_ptable(vm: *mut Vm) -> *mut PageTable<Stage2> {
    &mut (*vm).state.get_mut_unchecked().ptable
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_arch(vm: *mut Vm) -> *mut ArchVm {
    &mut (*vm).state.get_mut_unchecked().arch
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_vcpu_count(vm: *const Vm) -> spci_vcpu_count_t {
    (*vm).vcpu_count
}
