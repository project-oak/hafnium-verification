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

use core::ptr;
use core::sync::atomic::AtomicBool;
use arrayvec::ArrayVec;

use crate::cpu::*;
use crate::list::*;
use crate::mm::*;
use crate::mpool::*;
use crate::spinlock::*;
use crate::types::*;

pub enum MailboxState {
    /// There is no message in the mailbox.
    Empty,

    /// There is a message in the mailbox that is waiting for a reader.
    Received,

    /// There is a message in the mailbox that has been read.
    Read,
}

// TODO(@jeehoonkang)
struct SpciMessage {}

pub struct WaitEntry {
    /// The VM that is waiting for a mailbox to become writable.
    waiting_vm: *const Vm,

    /// Links used to add entry to a VM's waiter_list. This is protected by the notifying VM's lock.
    wait_links: ListEntry,

    /// Links used to add entry to a VM's ready_list. This is protected by the waiting VM's lock.
    ready_links: ListEntry,
}

impl Default for WaitEntry {
    fn default() -> Self {
        Self {
            waiting_vm: ptr::null(),
            wait_links: ListEntry::default(),
            ready_links: ListEntry::default(),
        }
    }
}

pub struct Mailbox {
    state: MailboxState,
    recv: *mut SpciMessage,
    send: *const SpciMessage,

    /// List of wait_entry structs representing VMs that want to be notified when the mailbox
    /// becomes writable. Once the mailbox does become writable, the entry is removed from this list
    /// and added to the waiting VM's ready_list.
    waiter_list: ListEntry,

    /// List of wait_entry structs representing VMs whose mailboxes became writable since the owner
    /// of the mailbox registers for notification.
    ready_list: ListEntry,
}

impl Mailbox {
    pub fn new() -> Self {
        Self {
            state: MailboxState::Empty,
            recv: ptr::null_mut(),
            send: ptr::null(),
            waiter_list: ListEntry::new(),
            ready_list: ListEntry::new(),
        }
    }
}

// TODO(@jeehoonkang)
pub struct VmState {
    pub ptable: PageTable<Stage2>,
    pub mailbox: Mailbox,
}

impl VmState {
    pub fn new(ptable: PageTable<Stage2>, mailbox: Mailbox) -> Self {
        Self { ptable, mailbox }
    }
}

// TODO(@jeehoonkang)
pub struct Vm {
    id: u32,
    pub state: SpinLock<VmState>,
    vcpus: ArrayVec<[VCpu; MAX_CPUS]>,

    wait_entries: [WaitEntry; MAX_VMS],
    aborting: AtomicBool,
}

impl Vm {
    pub fn new(id: u32, vcpu_count: u32, mpool: &MPool) -> Option<Self> {
        let ptable = PageTable::new(mpool)?;

        Some(Self {
            id,
            state: SpinLock::new(VmState::new(
                ptable, 
                Mailbox::new(),
            )),
            vcpus: ArrayVec::new(), // vm->vcpu_count = vcpu_count;
            wait_entries: unimplemented!(),
            aborting: AtomicBool::new(false),
        })
    }

	  // /* Initialise waiter entries. */
	  // for (i = 0; i < MAX_VMS; i++) {
	  // 	vm->wait_entries[i].waiting_vm = vm;
	  // 	list_init(&vm->wait_entries[i].wait_links);
	  // 	list_init(&vm->wait_entries[i].ready_links);
	  // }

	  // /* Do basic initialization of vcpus. */
	  // for (i = 0; i < vcpu_count; i++) {
	  // 	vcpu_init(vm_get_vcpu(vm, i), vm);
	  // }

	  // ++vm_count;
	  // *new_vm = vm;

    pub unsafe fn get_index(&self, vcpu: &VCpu) -> usize {
        (vcpu as *const VCpu).wrapping_offset_from(&self.vcpus[0] as *const _) as usize
    }
}

pub struct VmManager {
    vms: ArrayVec<[Vm; MAX_VMS]>,
}

impl VmManager {
    pub fn insert(&mut self, vm: Vm) -> Result<(), Vm> {
        self.vms.try_push(vm)
            .map_err(|e| e.element())
    }

    pub unsafe fn get_index(&self, vm: &Vm) -> usize {
        (vm as *const Vm).wrapping_offset_from(&self.vms[0] as *const _) as usize
    }
}


// TODO(@jeehoonkang)
pub struct ArchRegs {}

impl ArchRegs {
    pub const fn new() -> Self {
        unimplemented!()
    }

    pub fn set_pc_arg(&mut self, entry: usize, arg: uintreg_t) {
        unimplemented!()
    }

    pub fn reset(&mut self, is_primary: bool, vm_id: u64, vcpu_id: u64, table: usize) {
        unimplemented!()
    }
}
