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
use core::ops::{Deref, DerefMut};
use core::ptr;
use core::str;
use core::sync::atomic::AtomicBool;

use arrayvec::ArrayVec;
use scopeguard::guard;

use crate::addr::*;
use crate::arch::*;
use crate::cpu::*;
use crate::list::*;
use crate::mm::*;
use crate::mpool::*;
use crate::page::*;
use crate::singleton::*;
use crate::spci::*;
use crate::spinlock::*;
use crate::std::*;
use crate::types::*;

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
    wait_links: ListEntry,

    /// Links used to add entry to a VM's ready_list. This is protected by the waiting VM's lock.
    ready_links: ListEntry,
}

impl WaitEntry {
    #[inline]
    pub unsafe fn is_in_ready_list(&self) -> bool {
        !list_empty(&self.ready_links)
    }
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
    waiter_list: ListEntry,

    /// List of wait_entry structs representing VMs whose mailboxes became
    /// writable since the owner of the mailbox registers for notification.
    ready_list: ListEntry,
}

impl Mailbox {
    /// Initializes the mailbox.
    /// TODO(HfO2): Refactor `vm_init` and make `Mailbox::new()` instead of this.
    pub unsafe fn init(&mut self) {
        self.state = MailboxState::Empty;
        self.recv = ptr::null_mut();
        self.send = ptr::null();

        list_init(&mut self.waiter_list);
        list_init(&mut self.ready_list);
    }

    /// Retrieves the next waiter and removes it from the wait list if the VM's
    /// mailbox is in a writable state.
    pub unsafe fn fetch_waiter(&mut self) -> *mut WaitEntry {
        if self.state != MailboxState::Empty || self.recv.is_null() || list_empty(&self.waiter_list)
        {
            // The mailbox is not writable or there are no waiters.
            return ptr::null_mut();
        }

        // Remove waiter from the wait list.
        container_of!(list_pop_front(&self.waiter_list), WaitEntry, wait_links)
    }

    /// Checks if any waiters exists.
    pub fn is_waiter_list_empty(&self) -> bool {
        unsafe { list_empty(&self.waiter_list) }
    }

    /// Checks whether there exists a pending message. If one exists, marks the
    /// mailbox read.
    pub fn try_read(&mut self) -> Result<(), ()> {
        if self.state == MailboxState::Received {
            self.state = MailboxState::Read;
            Ok(())
        } else {
            Err(())
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
        local_page_pool: &MPool,
    ) -> Result<(), ()> {
        // TODO(HfO2): Acquring the singleton here is not recommended. Get the
        // hypervisor ptable from callee (API module.)
        let mut hypervisor_ptable = unsafe { MEMORY_MANAGER.get_ref() }.hypervisor_ptable.lock();
        let mut ptable = guard(hypervisor_ptable.deref_mut(), |_| ());

        // Map the send page as read-only in the hypervisor address space.
        if ptable
            .identity_map(pa_send_begin, pa_send_end, Mode::R, local_page_pool)
            .is_err()
        {
            // TODO: partial defrag of failed range.
            // Recover any memory consumed in failed mapping.
            ptable.defrag(local_page_pool);
            return Err(());
        }

        let mut ptable = guard(ptable, |mut ptable| {
            ptable
                .unmap(pa_send_begin, pa_send_end, local_page_pool)
                .unwrap();
        });

        // Map the receive page as writable in the hypervisor address space. On
        // failure, unmap the send page before returning.
        if ptable
            .identity_map(pa_recv_begin, pa_recv_end, Mode::W, local_page_pool)
            .is_err()
        {
            // TODO: parital defrag of failed range.
            // Recover any memory consumed in failed mapping.
            ptable.defrag(local_page_pool);
            return Err(());
        }

        // Forgetting `ptable` only skips dropping the nested `ScopeGuard`s.
        // `hypervisor_ptable` will be safely dropped and the lock will be
        // released.
        mem::forget(ptable);
        self.send = pa_addr(pa_send_begin) as usize as *const SpciMessage;
        self.recv = pa_addr(pa_recv_begin) as usize as *mut SpciMessage;
        Ok(())
    }

    pub fn get_send_ptr(&self) -> *const SpciMessage {
        self.send
    }

    pub fn get_recv_ptr(&self) -> *mut SpciMessage {
        self.recv
    }
}

pub struct VmInner {
    log_buffer: ArrayVec<[c_char; LOG_BUFFER_SIZE]>,
    pub ptable: PageTable<Stage2>,
    mailbox: Mailbox,

    /// Wait entries to be used when waiting on other VM mailboxes.
    wait_entries: [WaitEntry; MAX_VMS],
    arch: ArchVm,
}

impl VmInner {
    /// Initializes VmInner.
    pub unsafe fn init(&mut self, vm: *mut Vm, ppool: &MPool) -> Result<(), ()> {
        self.mailbox.init();

        if !mm_vm_init(&mut self.ptable, ppool) {
            return Err(());
        }

        // Initialise waiter entries.
        for i in 0..MAX_VMS {
            self.wait_entries[i].waiting_vm = vm;
            list_init(&mut self.wait_entries[i].wait_links);
            list_init(&mut self.wait_entries[i].ready_links);
        }

        Ok(())
    }

    /// Retrieves the next waiter and removes it from the wait list if the VM's
    /// mailbox is in a writable state.
    pub unsafe fn fetch_waiter(&mut self) -> *mut WaitEntry {
        self.mailbox.fetch_waiter()
    }

    /// Checks if any waiters exists.
    pub fn is_waiter_list_empty(&self) -> bool {
        self.mailbox.is_waiter_list_empty()
    }

    /// Checks whether there exists a pending message. If one exists, marks the
    /// mailbox read.
    pub fn try_read(&mut self) -> Result<(), ()> {
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
    #[inline]
    fn configure_pages(
        &mut self,
        pa_send_begin: paddr_t,
        pa_send_end: paddr_t,
        orig_send_mode: Mode,
        pa_recv_begin: paddr_t,
        pa_recv_end: paddr_t,
        orig_recv_mode: Mode,
        fallback_mpool: &MPool,
    ) -> Result<(), ()> {
        // Create a local pool so any freed memory can't be used by another
        // thread. This is to ensure the original mapping can be restored if
        // any stage of the process fails.
        let local_page_pool: MPool = MPool::new_with_fallback(fallback_mpool);
        let mut ptable = guard(&mut self.ptable, |_| ());

        // Take memory ownership away from the VM and mark as shared.
        ptable.identity_map(
            pa_send_begin,
            pa_send_end,
            Mode::UNOWNED | Mode::SHARED | Mode::R | Mode::W,
            &local_page_pool,
        )?;

        let mut ptable = guard(ptable, |mut ptable| {
            ptable
                .identity_map(pa_send_begin, pa_send_end, orig_send_mode, &local_page_pool)
                .unwrap();
        });

        ptable
            .identity_map(
                pa_recv_begin,
                pa_recv_end,
                Mode::UNOWNED | Mode::SHARED | Mode::R,
                &local_page_pool,
            )
            .map_err(|_| {
                // TODO: partial defrag of failed range.
                // Recover any memory consumed in failed mapping.
                ptable.defrag(&local_page_pool);
            })?;

        let ptable = guard(ptable, |mut ptable| {
            ptable
                .identity_map(pa_recv_begin, pa_recv_end, orig_recv_mode, &local_page_pool)
                .unwrap();
        });

        self.mailbox.configure_stage1(
            pa_send_begin,
            pa_send_end,
            pa_recv_begin,
            pa_recv_end,
            &local_page_pool,
        )?;

        mem::forget(ptable);
        Ok(())
    }

    /// Configures the VM to send/receive data through the specified pages. The
    /// pages must not be shared.
    ///
    /// Returns:
    ///  - None on failure.
    ///  - Some(()) on success.
    pub fn configure(
        &mut self,
        send: ipaddr_t,
        recv: ipaddr_t,
        fallback_mpool: &MPool,
    ) -> Result<(), ()> {
        // Fail if addresses are not page-aligned.
        if !is_aligned(ipa_addr(send), PAGE_SIZE) || !is_aligned(ipa_addr(recv), PAGE_SIZE) {
            return Err(());
        }

        // Convert to physical addresses.
        let pa_send_begin = pa_from_ipa(send);
        let pa_send_end = pa_add(pa_send_begin, PAGE_SIZE);

        let pa_recv_begin = pa_from_ipa(recv);
        let pa_recv_end = pa_add(pa_recv_begin, PAGE_SIZE);

        // Fail if the same page is used for the send and receive pages.
        if pa_addr(pa_send_begin) == pa_addr(pa_recv_begin) {
            return Err(());
        }

        // We only allow these to be setup once.
        if self.is_configured() {
            return Err(());
        }

        // Ensure the pages are valid, owned and exclusive to the VM and that
        // the VM has the required access to the memory.
        let orig_send_mode = self.ptable.get_mode(send, ipa_add(send, PAGE_SIZE))?;
        if !(orig_send_mode.valid_owned_exclusive() && orig_send_mode.contains(Mode::R | Mode::W)) {
            return Err(());
        }

        let orig_recv_mode = self.ptable.get_mode(recv, ipa_add(recv, PAGE_SIZE))?;
        if !(orig_recv_mode.valid_owned_exclusive() && orig_recv_mode.contains(Mode::R)) {
            return Err(());
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

            let list_entry = list_pop_front(&self.mailbox.ready_list);
            let entry: *mut WaitEntry = container_of!(list_entry, WaitEntry, ready_links);
            let ret = entry.offset_from(self.wait_entries.as_ptr()) as spci_vm_id_t;
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
    pub fn wait_for(&mut self, target: &mut Self, target_id: spci_vm_id_t) -> Result<(), ()> {
        let entry = &mut self.wait_entries[target_id as usize];

        // Append waiter only if it's not there yet.
        if unsafe { !list_empty(&(*entry).wait_links) } {
            return Err(());
        }

        unsafe {
            list_append(&mut target.mailbox.waiter_list, &mut (*entry).wait_links);
        }
        Ok(())
    }

    pub fn get_send_ptr(&self) -> *const SpciMessage {
        self.mailbox.get_send_ptr()
    }

    pub fn get_recv_ptr(&self) -> *mut SpciMessage {
        self.mailbox.get_recv_ptr()
    }

    pub fn debug_log(&mut self, id: spci_vm_id_t, c: c_char) {
        if c == '\n' as u32 as u8 || c == '\0' as u32 as u8 || self.log_buffer.is_full() {
            // flush the buffer.
            let log = str::from_utf8(&self.log_buffer).unwrap_or("non-UTF8 bytes");
            dlog!("VM {}: {}\n", id, log);
            self.log_buffer.clear();
        } else {
            self.log_buffer.push(c);
        }
    }
}

pub struct Vm {
    pub id: spci_vm_id_t,

    /// VCpus of this vm.
    /// Note: This field is regarded as a kind of mutable states of Vm, but is
    /// not contained in VmInner, because
    ///   1. Mutable inner fields are contained in VCpuState.
    ///   2. VCpuState has higher lock order than one of Vm. It is nonsense to
    ///      lock VmInner to acquire VCpuState.
    pub vcpus: ArrayVec<[VCpu; MAX_CPUS]>,

    /// See api.c for the partial ordering on locks.
    pub inner: SpinLock<VmInner>,
    pub aborting: AtomicBool,
}

impl Vm {
    pub fn init(
        &mut self,
        id: spci_vm_id_t,
        vcpu_count: spci_vcpu_count_t,
        ppool: &MPool,
    ) -> Result<(), ()> {
        self.id = id;
        self.vcpus = ArrayVec::new();
        self.aborting = AtomicBool::new(false);
        unsafe {
            let self_ptr = self as *mut _;
            self.inner.get_mut().init(self_ptr, ppool)?;

            for _ in 0..vcpu_count {
                self.vcpus.push(VCpu::new(self_ptr));
            }
        }
        Ok(())
    }

    /// Returns the root address of the page table of this VM. It is safe not to
    /// lock `self.inner` because the value of `ptable.as_raw()` doesn't change
    /// after `ptable` is initialized. Of course, actual page table may vary
    /// during running. That's why this function returns `paddr_t` rather than
    /// `&RawPage`.
    pub fn get_ptable_raw(&self) -> paddr_t {
        unsafe { self.inner.get_unchecked().ptable.as_raw() }
    }

    pub fn debug_log(&self, c: c_char) {
        self.inner.lock().debug_log(self.id, c)
    }
}

/// Encapsulates a VM whose lock is held.
#[repr(C)]
#[derive(PartialEq, Eq)]
pub struct VmLocked {
    vm: *mut Vm,
}

impl Drop for VmLocked {
    fn drop(&mut self) {
        unsafe {
            (*self.vm).inner.unlock_unchecked();
        }
    }
}

impl Deref for VmLocked {
    type Target = Vm;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.vm }
    }
}

impl VmLocked {
    #[inline]
    pub unsafe fn from_raw(vm: *mut Vm) -> Self {
        Self { vm }
    }

    #[inline]
    pub fn into_raw(self) -> *mut Vm {
        let ret = self.vm;
        mem::forget(self);
        ret
    }

    #[inline]
    pub fn get_inner(&self) -> &VmInner {
        unsafe { (*self.vm).inner.get_unchecked() }
    }

    #[inline]
    pub fn get_inner_mut(&mut self) -> &mut VmInner {
        unsafe { (*self.vm).inner.get_mut_unchecked() }
    }
}

pub struct VmManager {
    vms: ArrayVec<[Vm; MAX_VMS]>,
}

impl VmManager {
    pub fn new() -> Self {
        Self {
            vms: ArrayVec::new(),
        }
    }

    pub fn new_vm(&mut self, vcpu_count: spci_vcpu_count_t, ppool: &MPool) -> Option<&mut Vm> {
        if self.vms.is_full() {
            return None;
        }

        let id = self.vms.len();
        let vm = unsafe { self.vms.get_unchecked_mut(id) };

        vm.init(id as u16, vcpu_count, ppool).ok()?;

        unsafe {
            self.vms.set_len(id + 1);
        }

        Some(&mut self.vms[id])
    }

    pub fn get(&self, id: spci_vm_id_t) -> Option<&Vm> {
        self.vms.get(id as usize)
    }

    pub fn get_mut(&mut self, id: spci_vm_id_t) -> Option<&mut Vm> {
        self.vms.get_mut(id as usize)
    }
}

#[no_mangle]
pub unsafe extern "C" fn vm_init(
    vcpu_count: spci_vcpu_count_t,
    ppool: *mut MPool,
    new_vm: *mut *mut Vm,
) -> bool {
    match VM_MANAGER.get_mut().new_vm(vcpu_count, &mut *ppool) {
        Some(vm) => {
            *new_vm = vm as *mut _;
            true
        }
        None => false,
    }
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_count() -> spci_vm_count_t {
    VM_MANAGER.get_ref().vms.len() as spci_vm_count_t
}

#[no_mangle]
pub unsafe extern "C" fn vm_find(id: spci_vm_id_t) -> *mut Vm {
    VM_MANAGER
        .get_mut()
        .vms
        .get_mut(id as usize)  // Ensure the VM is initialized.
        .map(|vm| vm as *mut _)
        .unwrap_or(ptr::null_mut())
}

/// Locks the given VM and updates `locked` to hold the newly locked vm.
#[no_mangle]
pub unsafe extern "C" fn vm_lock(vm: *mut Vm) -> VmLocked {
    mem::forget((*vm).inner.lock());
    VmLocked { vm }
}

/// Unlocks a VM previously locked with vm_lock, and updates `locked` to reflect
/// the fact that the VM is no longer locked.
#[no_mangle]
pub unsafe extern "C" fn vm_unlock(locked: *mut VmLocked) {
    drop(ptr::read(locked));
    (*locked).vm = ptr::null_mut();
}

/// Get the vCPU with the given index from the given VM.
/// This assumes the index is valid, i.e. less than vm->vcpu_count.
#[no_mangle]
pub unsafe extern "C" fn vm_get_vcpu(vm: *mut Vm, vcpu_index: spci_vcpu_index_t) -> *mut VCpu {
    assert!((vcpu_index as usize) < (*vm).vcpus.len());
    &mut (*vm).vcpus[vcpu_index as usize]
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_id(vm: *const Vm) -> spci_vm_id_t {
    (*vm).id
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_ptable(vm: *mut Vm) -> *mut PageTable<Stage2> {
    &mut (*vm).inner.get_mut_unchecked().ptable
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_arch(vm: *mut Vm) -> *mut ArchVm {
    &mut (*vm).inner.get_mut_unchecked().arch
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_vcpu_count(vm: *const Vm) -> spci_vcpu_count_t {
    (*vm).vcpus.len() as spci_vcpu_count_t
}
