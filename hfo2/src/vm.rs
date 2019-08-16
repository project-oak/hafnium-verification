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

const LOG_BUFFER_SIZE: usize = 256;

#[repr(C)]
#[derive(PartialEq)]
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
    pub state: MailboxState,
    pub recv: *mut SpciMessage,
    pub send: *const SpciMessage,

    /// List of wait_entry structs representing VMs that want to be notified when the mailbox
    /// becomes writable. Once the mailbox does become writable, the entry is removed from this list
    /// and added to the waiting VM's ready_list.
    pub waiter_list: list_entry,

    /// List of wait_entry structs representing VMs whose mailboxes became writable since the owner
    /// of the mailbox registers for notification.
    pub ready_list: list_entry,
}

struct VmState {
    log_buffer: ArrayVec<[c_char; LOG_BUFFER_SIZE]>,
}

impl VmState {
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
    /// See api.c for the partial ordering on locks.
    pub lock: RawSpinLock,
    pub vcpu_count: spci_vcpu_count_t,
    pub vcpus: [VCpu; MAX_CPUS],
    pub ptable: PageTable<Stage2>,
    pub mailbox: Mailbox,
    state: SpinLock<VmState>,

    /// Wait entries to be used when waiting on other VM mailboxes.
    pub wait_entries: [WaitEntry; MAX_VMS],
    pub aborting: AtomicBool,
    pub arch: ArchVm,
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

    list_init(&mut (*vm).mailbox.waiter_list);
    list_init(&mut (*vm).mailbox.ready_list);
    sl_init(&mut (*vm).lock);

    (*vm).id = vm_count;
    (*vm).vcpu_count = vcpu_count;
    (*vm).mailbox.state = MailboxState::Empty;
    (*vm).aborting = AtomicBool::new(false);

    if !mm_vm_init(&mut (*vm).ptable, ppool) {
        return false;
    }

    // Initialise waiter entries.
    for i in 0..MAX_VMS {
        (*vm).wait_entries[i].waiting_vm = vm;
        list_init(&mut (*vm).wait_entries[i].wait_links);
        list_init(&mut (*vm).wait_entries[i].ready_links);
    }

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

    sl_lock(&(*vm).lock);

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

    sl_lock_both(&(*vm1).lock, &(*vm2).lock);

    dual_lock
}

/// Unlocks a VM previously locked with vm_lock, and updates `locked` to reflect
/// the fact that the VM is no longer locked.
#[no_mangle]
pub unsafe extern "C" fn vm_unlock(locked: *mut VmLocked) {
    sl_unlock(&(*(*locked).vm).lock);
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
    &mut (*vm).ptable
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_arch(vm: *mut Vm) -> *mut ArchVm {
    &mut (*vm).arch
}

#[no_mangle]
pub unsafe extern "C" fn vm_get_vcpu_count(vm: *const Vm) -> spci_vcpu_count_t {
    (*vm).vcpu_count
}
