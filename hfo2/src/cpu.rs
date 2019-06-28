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

use crate::mm::Mode;
use crate::spinlock::*;
use crate::types::*;
use crate::vm::*;

extern "C" {
    fn arch_irq_enable();
    fn arch_irq_disable();
}

/// The number of bits in each element of the interrupt bitfields.
const INTERRUPT_REGISTER_BITS: usize = 32;

pub enum VCpuStatus {
    /// The vcpu is switched off.
    Off,

    /// The vcpu is ready to be run.
    Ready,

    /// The vcpu is currently running.
    Running,

    /// The vcpu is waiting for a message.
    BlockedMailbox,

    /// The vcpu is waiting for an interrupt.
    BlockedInterrupt,

    /// The vcpu has aborted.
    Aborted,
}

pub struct VCpuState {
    cpu: *const Cpu,
    status: VCpuStatus,
    regs: ArchRegs,
}

impl VCpuState {
    pub const fn new(status: VCpuStatus, regs: ArchRegs) -> Self {
        Self {
            cpu: ptr::null(),
            status,
            regs,
        }
    }

    pub fn on(&mut self, entry: usize, arg: uintreg_t) {
        self.status = VCpuStatus::Ready;
        self.regs.set_pc_arg(entry, arg);
    }
}

pub struct Interrupts {
    /// Bitfield keeping track of which interrupts are enabled.
    enabled: [u32; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],

    /// Bitfield keeping track of which interrupts are pending.
    pending: [u32; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],

    /// The number of interrupts which are currently both enabled and pending. i.e. the number of
    /// bits set in enabled & pending.
    enabled_and_pending_count: u32,
}

impl Interrupts {
    pub const fn new() -> Self {
        Self {
            enabled: [0; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],
            pending: [0; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],
            enabled_and_pending_count: 0,
        }
    }

    /// Assuming that the arguments have already been checked by the caller, injects a virtual
    /// interrupt of the given ID into the given target vCPU. This doesn't cause the vCPU to
    /// actually be run immediately; it will be taken when the vCPU is next run, which is up to the
    /// scheduler.
    ///
    /// Returns:
    /// - false on success if no further action is needed.
    /// - true if it was called by the primary VM and the primary VM now needs to wake up or kick
    ///   the target vCPU.
    pub fn inject(&mut self, intid: usize) -> bool {
        let intid_index = intid / INTERRUPT_REGISTER_BITS;
        let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS);

        let enabled = self.enabled[intid_index];
        let pending = self.pending[intid_index];
        self.pending[intid_index] |= intid_mask;

        // We only need to change state and (maybe) trigger a virtual IRQ if it is enabled and was
        // not previously pending. Otherwise we can skip everything except setting the pending bit.
        //
        // If you change this logic make sure to update the need_vm_lock logic above to match.
        if enabled & !pending & intid_mask == 0 {
            return false;
        }

        // Increment the count.
        self.enabled_and_pending_count += 1;

        // Only need to update state if there was not already an interrupt enabled and pending.
        if self.enabled_and_pending_count != 1 {
            return false;
        }

        true
    }

    /// Enables or disables a given interrupt ID for the calling vCPU.
    ///
    /// Returns true on success, or false if the intid is invalid.
    pub fn enable(&mut self, intid: usize, enable: bool) -> bool {
        let intid_index = intid / INTERRUPT_REGISTER_BITS;
        let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS);

        if intid >= HF_NUM_INTIDS {
            return false;
        }

        let enabled = self.enabled[intid_index];
        let pending = self.pending[intid_index];

        if enable {
            // If it is pending and was not enabled before, increment the count.
            if pending & !enabled & intid_mask != 0 {
                self.enabled_and_pending_count += 1;
            }
            self.enabled[intid_index] |= intid_mask;
        } else {
            // If it is pending and was enabled before, decrement the count.
            if pending & enabled & intid_mask != 0 {
                self.enabled_and_pending_count -= 1;
            }
            self.enabled[intid_index] &= !intid_mask;
        }

        true
    }
}

#[repr(C)]
pub struct VCpuFaultInfo {
    ipaddr: usize,
    vaddr: usize,
    pc: usize,
    mode: Mode,
}

pub struct VCpu {
    vm: *const Vm,

    /// The state is only changed in the context of the vCPU being run. This ensures the scheduler
    /// can easily keep track of the vCPU state as transitions are indicated by the return code from
    /// the run call.
    state: SpinLock<VCpuState>,

    interrupts: SpinLock<Interrupts>,
}

impl VCpu {
    pub const fn new(vm: *const Vm) -> Self {
        Self {
            vm,
            state: SpinLock::new(VCpuState::new(VCpuStatus::Off, ArchRegs::new())),
            interrupts: SpinLock::new(Interrupts::new()),
        }
    }

    /// Initialise the registers for the given vCPU and set the state to VCPU_STATE_READY. The
    /// caller must hold the vCPU lock while calling this.
    fn on(&mut self, entry: usize, arg: uintreg_t) {
        let state = self.state.get_mut().on(entry, arg);
    }

    /// Starts a vCPU of a secondary VM.
    fn secondary_reset_start(&self, entry: usize, arg: uintreg_t) {
        assert!(true, "TODO: vcpu->vm->id != HF_PRIMARY_VM_ID");

        // Set vCPU registers to a clean state ready for boot. As this is a secondary which can
        // migrate between pCPUs, the ID of the vCPU is defined as the index and does not match the
        // ID of the pCPU it is running on.
        let mut state = self.state.lock();
        state
            .regs
            .reset(false, unimplemented!(), unimplemented!(), unimplemented!());
        state.on(entry, arg);
    }

    fn get_vm(&self) -> &Vm {
        unsafe { &*self.vm }
    }

    fn get_index(&self) -> usize {
        unsafe { self.get_vm().get_index(self) }
    }

    /// Handles a page fault. It does so by determining if it's a legitimate or spurious fault, and
    /// recovering from the latter.
    ///
    /// Returns true if the caller should resume the current vcpu, or false if its VM should be
    /// aborted.
    fn handle_page_fault(&self, f: &VCpuFaultInfo) -> bool {
        let mask = f.mode | Mode::INVALID;

        // Check if this is a legitimate fault, i.e., if the page table doesn't allow the access
        // attemped by the VM.
        //
        // Otherwise, this is a spurious fault, likely because another CPU is updating the page
        // table. It is responsible for issuing global TLB invalidations while holding the VM lock,
        // so we don't need to do anything else to recover from it. (Acquiring/releasing the lock
        // ensured that the invalidations have completed.)
        let resume = self
            .get_vm()
            .state
            .lock()
            .ptable
            .get_mode(f.ipaddr, f.ipaddr + 1)
            .map(|mode| mode & mask == f.mode)
            .unwrap_or(false);

        if !resume {
            dlog!("Stage-2 page fault: pc={:X}, vmid={}, vcpu={}, vaddr={:X}, ipaddr={:X}, mode={:X}\n",
		              f.pc,
                  (unimplemented!("vm->id"), 0).1,
                  self.get_index(),
                  f.vaddr,
                  f.ipaddr,
                  f.mode,
            );
        }

        resume
    }
}

// TODO: Update alignment such that cpus are in different cache lines.
#[repr(C)]
pub struct Cpu {
    /// CPU identifier. Doesn't have to be contiguous.
    id: u64,

    /// Pointer to bottom of the stack.
    stack_bottom: *const c_void,

    /// Enabling/disabling irqs are counted per-cpu. They are enabled when the count is zero, and
    /// disabled when it's non-zero.
    irq_disable_count: u32,

    /// See api.c for the partial ordering on locks.
    lock: RawSpinLock,

    /// Determines whether or not the cpu is currently on.
    is_on: bool,
}

impl Cpu {
    pub const fn new() -> Self {
        Self {
            id: 0,
            stack_bottom: ptr::null(),
            irq_disable_count: 0,
            lock: RawSpinLock::new(),
            is_on: false,
        }
    }

    pub fn irq_enable(&mut self) {
        self.irq_disable_count -= 1;
        if self.irq_disable_count == 0 {
            unsafe {
                arch_irq_enable();
            }
        }
    }

    pub fn irq_disable(&mut self) {
        if self.irq_disable_count == 0 {
            unsafe {
                arch_irq_disable();
            }
        }
        self.irq_disable_count += 1;
    }

    /// Turns CPU on and returns the previous state.
    pub fn on(&mut self, entry: usize, arg: uintreg_t) -> bool {
        self.lock.lock();
        let prev = self.is_on;
        self.is_on = true;
        self.lock.unlock();

        if !prev {
            let vm = unimplemented!();
            let vcpu: VCpu = unimplemented!();
            vcpu.on(entry, arg);
        }

        prev
    }

    /// Prepares the CPU for turning itself off.
    pub fn off(&mut self) {
        self.lock.lock();
        self.is_on = false;
        self.lock.unlock();
    }
}
