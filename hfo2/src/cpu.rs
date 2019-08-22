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

use crate::addr::*;
use crate::arch::*;
use crate::mm::*;
use crate::page::*;
use crate::spinlock::*;
use crate::std::*;
use crate::types::*;
use crate::vm::*;

/// From inc/hf/arch/cpu.h.
extern "C" {
    /// Disables interrupts.
    fn arch_irq_enable();

    /// Enables interrupts.
    fn arch_irq_disable();

    /// Reset the register values other than the PC and argument which are set with
    /// `arch_regs_set_pc_arg()`.
    fn arch_regs_reset(
        r: *mut ArchRegs,
        is_primary: bool,
        vm_id: spci_vm_id_t,
        vcpu_id: cpu_id_t,
        table: paddr_t,
    );

    /// Updates the given registers so that when a vcpu runs, it starts off at the
    /// given address (pc) with the given argument.
    ///
    /// This function must only be called on an arch_regs that is known not be in use
    /// by any other physical CPU.
    fn arch_regs_set_pc_arg(r: *mut ArchRegs, pc: ipaddr_t, arg: uintreg_t);

    /// Updates the register holding the return value of a function.
    ///
    /// This function must only be called on an arch_regs that is known not be in use
    /// by any other physical CPU.
    fn arch_regs_set_retval(r: *mut ArchRegs, v: uintreg_t);
}

const STACK_SIZE: usize = PAGE_SIZE;

/// The number of bits in each element of the interrupt bitfields.
pub const INTERRUPT_REGISTER_BITS: usize = 32;

#[repr(C)]
#[derive(PartialEq)]
pub enum VCpuStatus {
    /// The vcpu is switched off.
    Off,

    /// The vcpu is ready to be run.
    Ready,

    /// The vcpu is waiting for a message.
    BlockedMailbox,

    /// The vcpu is waiting for an interrupt.
    BlockedInterrupt,

    /// The vcpu has aborted.
    Aborted,
}

#[repr(C)]
pub struct Interrupts {
    /// Bitfield keeping track of which interrupts are enabled.
    pub enabled: [u32; HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS],

    /// Bitfield keeping track of which interrupts are pending.
    pub pending: [u32; HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS],

    /// The number of interrupts which are currently both enabled and pending. i.e. the number of
    /// bits set in enabled & pending.
    pub enabled_and_pending_count: u32,
}

impl Interrupts {
    pub fn id_to_index(intid: intid_t) -> Option<(usize, u32)> {
        if intid >= HF_NUM_INTIDS {
            return None;
        }

        let intid_index = intid as usize / INTERRUPT_REGISTER_BITS;
        let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS as u32);

        Some((intid_index, intid_mask))
    }

    /// injects a virtual interrupt of the given ID into the given target vCPU.
    /// Returns:
    ///  - None if no further action is needed.
    ///  - Some(()) if the vcpu had have no pending interrupt before, thus
    ///    proper scheduling is required.
    pub fn inject(&mut self, intid: intid_t) -> Option<()> {
        let (intid_index, intid_mask) = Self::id_to_index(intid)?;
        // We only need to change state and (maybe) trigger a virtual IRQ if it
        // is enabled and was not previously pending. Otherwise we can skip
        // everything except setting the pending bit.
        //
        // If you change this logic make sure to update the need_vm_lock logic
        // above to match.
        let ret = {
            if self.enabled[intid_index] & !self.pending[intid_index]
               & intid_mask == 0
            {
                None
            } else {
                // Increment the count.
                self.enabled_and_pending_count += 1;

                // Only need to update state if there was not already an 
                // interrupt enabled and pending.
                if self.enabled_and_pending_count != 1 {
                    None
                } else {
                    Some(())
                }
            }            
        };

        // Either way, make it pending.
        self.pending[intid_index] |= intid_mask;
        ret
    }

    /// Enables or disables a given interrupt ID for the calling vCPU.
    pub fn enable(&mut self, intid: intid_t, enable: bool) -> Option<()> {
        let (intid_index, intid_mask) = Self::id_to_index(intid)?;

        if enable {
            // If it is pending and was not enabled before, increment the count.
            if (self.pending[intid_index]
                & !self.enabled[intid_index]
                & intid_mask)
                != 0
            {
                self.enabled_and_pending_count += 1;
            }
            self.enabled[intid_index] |= intid_mask;
        } else {
            // If it is pending and was enabled before, decrement the count.
            if (self.pending[intid_index]
                & self.enabled[intid_index]
                & intid_mask)
                != 0
            {
                self.enabled_and_pending_count -= 1;
            }
            self.enabled[intid_index] &= !intid_mask;
        }

        Some(())
    }

    /// Returns the ID of the next pending interrupt for the calling vCPU, and
    /// acknowledges it (i.e. marks it as no longer pending). Returns
    /// HF_INVALID_INTID if there are no pending interrupts.
    pub fn get(&mut self) -> intid_t {
        let mut first_interrupt = HF_INVALID_INTID;

        // Find the first enabled pending interrupt ID, returns it, and
        // deactive it.
        for i in 0..(HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS) {
            let enabled_and_pending =
                self.enabled[i] & self.pending[i];
            if enabled_and_pending != 0 {
                let bit_index = enabled_and_pending.trailing_zeros();

                // Mark it as no longer pending and decrement the count.
                self.pending[i] &= !(1u32 << bit_index);
                self.enabled_and_pending_count -= 1;
                first_interrupt = (i * INTERRUPT_REGISTER_BITS) as u32 + bit_index;
                break;
            }
        }

        first_interrupt
    }
}

impl ArchRegs {
    /// Reset the register values other than the PC and argument which are set
    /// with `arch_regs_set_pc_arg()`.
    pub fn reset(&mut self, is_primary: bool, vm: &Vm, vcpu_id: cpu_id_t) {
        unsafe {
            arch_regs_reset(
                self,
                is_primary,
                vm.id,
                vcpu_id,
                vm.get_ptable_raw(),
            )
        }
    }

    /// Updates the register holding the return value of a function.
    pub fn set_retval(&mut self, v: uintreg_t) {
        unsafe {
            arch_regs_set_retval(self, v)
        }
    }

    /// Updates the given registers so that when a vcpu runs, it starts off at
    /// the given address (pc) with the given argument.
    pub fn set_pc_arg(&mut self, pc: ipaddr_t, arg: uintreg_t) {
        unsafe {
            arch_regs_set_pc_arg(self, pc, arg)
        }
    }
}

#[repr(C)]
pub struct VCpuFaultInfo {
    ipaddr: ipaddr_t,
    vaddr: vaddr_t,
    pc: vaddr_t,
    mode: Mode,
}

pub struct VCpuState {
    /// The state is only changed in the context of the vCPU being run. This 
    /// ensures the scheduler can easily keep track of the vCPU state as 
    /// transitions are indicated by the return code from the run call.
    pub state: VCpuStatus,
    pub cpu: *mut Cpu,
    pub regs: ArchRegs,
}

impl VCpuState {
    /// Initialise the registers for the given vCPU and set the state to
    /// VCpuStatus::Ready. The caller must hold the vCPU execution lock while
    /// calling this.
    pub fn on(&mut self, entry: ipaddr_t, arg: uintreg_t) {
        self.regs.set_pc_arg(entry, arg);
        self.state = VCpuStatus::Ready;
    }

    /// Check whether the given vcpu_state is an off state, for the purpose of
    /// turning vCPUs on and off. Note that aborted still counts as on in this
    /// context.
    pub fn is_off(&self) -> bool {
        match self.state {
            VCpuStatus::Off => true,
            _ =>
            // Aborted still counts as ON for the purposes of PSCI,
            // because according to the PSCI specification (section
            // 5.7.1) a core is only considered to be off if it has
            // been turned off with a CPU_OFF call or hasn't yet
            // been turned on with a CPU_ON call.
            {
                false
            }
        }
    }
}

#[repr(C)]
pub struct VCpu {
    pub vm: *mut Vm,

    /// If a vCPU is running, its lock is logically held by the running pCPU.
    pub state: SpinLock<VCpuState>,
    pub interrupts: SpinLock<Interrupts>,
}

/// Encapsulates a vCPU whose lock is held.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct VCpuExecutionLocked {
    vcpu: *mut VCpu,
}

// TODO: Update alignment such that cpus are in different cache lines.
#[repr(C)]
pub struct Cpu {
    /// CPU identifier. Doesn't have to be contiguous.
    pub id: cpu_id_t,

    /// Pointer to bottom of the stack.
    /// `pub` here is only required by `arch_cpu_module_init`.
    pub stack_bottom: *mut c_void,

    /// Enabling/disabling irqs are counted per-cpu. They are enabled when the count is zero, and
    /// disabled when it's non-zero.
    irq_disable_count: u32,

    /// See api.c for the partial ordering on locks.
    lock: RawSpinLock,

    /// Determines whether or not the cpu is currently on.
    is_on: bool,
}

// unsafe impl Sync for Cpu {}

/// The stack to be used by the CPUs.
/// TODO: alignas(2 * sizeof(uintreg_t))
#[no_mangle]
static mut callstacks: MaybeUninit<[[u8; STACK_SIZE]; MAX_CPUS]> = MaybeUninit::uninit();

/// State of all supported CPUs. The stack of the first one is initialized.
/// Kernel loader writes booted CPU ID on `cpus.id` and initializes the CPU
/// stack by the address in `cpus.stack_bottom`.
/// (See src/arch/aarch64/hypervisor/plat_entry.S and cpu_entry.S.)
///
/// Initializing static variables with pointers in Rust failed here. We left
/// the initialization code of `cpus` in `src/cpu.c`.
extern "C" {
    #[no_mangle]
    static mut cpus: MaybeUninit<[Cpu; MAX_CPUS]>;
}

static mut cpu_count: u32 = 1;

#[no_mangle]
pub unsafe extern "C" fn cpu_init(c: *mut Cpu) {
    // TODO: Assumes that c is zeroed out already.
    sl_init(&mut (*c).lock);
}

#[no_mangle]
pub unsafe extern "C" fn cpu_module_init(cpu_ids: *mut cpu_id_t, count: usize) {
    let mut j: u32;
    let boot_cpu_id: cpu_id_t = cpus.get_ref()[0].id;
    let mut found_boot_cpu: bool = false;

    arch_cpu_module_init();

    cpu_count = count as u32;

    // Initialize CPUs with the IDs from the configuration passed in. The
    // CPUs after the boot CPU are initialized in reverse order. The boot
    // CPU is initialized when it is found or in place of the last CPU if it
    // is not found.
    j = cpu_count;
    for i in 0..cpu_count {
        let c: *mut Cpu;
        let id: cpu_id_t = *cpu_ids.offset(i as isize);

        if found_boot_cpu || id != boot_cpu_id {
            j -= 1;
            c = &mut cpus.get_mut()[j as usize];
        } else {
            found_boot_cpu = true;
            c = &mut cpus.get_mut()[0];
        }

        cpu_init(c);
        (*c).id = id;
        {
            let callstacks_i = callstacks.get_mut()[i as usize].as_mut_ptr();
            (*c).stack_bottom = &mut *callstacks_i.offset(STACK_SIZE as isize) as *mut _ as _;

            // Note: referencing callstacks.get_mut()[i as usize][STACK_SIZE] directly
            // causes 'index out of bounds' error on compile time.
        }
    }

    if !found_boot_cpu {
        // Boot CPU was initialized but with wrong ID.
        dlog!("Boot CPU's ID not found in config.");
        cpus.get_mut()[0].id = boot_cpu_id;
    }
}

#[no_mangle]
pub unsafe extern "C" fn cpu_index(c: *mut Cpu) -> usize {
    c.offset_from(cpus.get_ref().as_ptr()) as usize
}

/// Turns CPU on and returns the previous state.
#[no_mangle]
pub unsafe extern "C" fn cpu_on(c: *mut Cpu, entry: ipaddr_t, arg: uintreg_t) -> bool {
    let prev: bool;

    sl_lock(&(*c).lock);
    prev = (*c).is_on;
    (*c).is_on = true;
    sl_unlock(&(*c).lock);

    if !prev {
        let vm = vm_find(HF_PRIMARY_VM_ID);
        let vcpu = vm_get_vcpu(vm, cpu_index(c) as u16);

        (*vcpu).state.lock().on(entry, arg);
    }

    prev
}

/// Prepares the CPU for turning itself off.
#[no_mangle]
pub unsafe extern "C" fn cpu_off(c: *mut Cpu) {
    sl_lock(&(*c).lock);
    (*c).is_on = true;
    sl_unlock(&(*c).lock);
}

/// Searches for a CPU based on its id.
#[no_mangle]
pub unsafe extern "C" fn cpu_find(id: cpu_id_t) -> *mut Cpu {
    for i in 0usize..cpu_count as usize {
        if cpus.get_ref()[i].id == id {
            return &mut cpus.get_mut()[i];
        }
    }

    ptr::null_mut()
}

/// Locks the given vCPU and updates `locked` to hold the newly locked vCPU.
#[no_mangle]
pub unsafe extern "C" fn vcpu_lock(vcpu: *mut VCpu) -> VCpuExecutionLocked {
    (*vcpu).state.lock().into_raw();

    VCpuExecutionLocked { vcpu }
}

/// Tries to lock the given vCPU, and updates `locked` if succeed.
#[no_mangle]
pub unsafe extern "C" fn vcpu_try_lock(vcpu: *mut VCpu, locked: *mut VCpuExecutionLocked) -> bool {
    match (*vcpu).state.try_lock() {
        Some(guard) => {
            guard.into_raw();
            *locked = VCpuExecutionLocked { vcpu };
            true
        },
        None => false,
    }
}

/// Unlocks a vCPU previously locked with vcpu_lock, and updates `locked` to
/// reflect the fact that the vCPU is no longer locked.
#[no_mangle]
pub unsafe extern "C" fn vcpu_unlock(locked: *mut VCpuExecutionLocked) {
    (*(*locked).vcpu).state.unlock_unchecked();
    (*locked).vcpu = ptr::null_mut();
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_init(vcpu: *mut VCpu, vm: *mut Vm) {
    memset_s(vcpu as _, mem::size_of::<VCpu>(), 0, mem::size_of::<VCpu>());
    (*vcpu).vm = vm;
    (*vcpu).state.get_mut_unchecked().state = VCpuStatus::Off;
}

/// Initialise the registers for the given vCPU and set the state to
/// VCpuStatus::Ready. The caller must hold the vCPU execution lock while
/// calling this.
#[no_mangle]
pub unsafe extern "C" fn vcpu_on(vcpu: VCpuExecutionLocked, entry: ipaddr_t, arg: uintreg_t) {
    (*vcpu.vcpu).state.get_mut_unchecked().on(entry, arg);
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_index(vcpu: *const VCpu) -> spci_vcpu_index_t {
    let vcpus = (*(*vcpu).vm).vcpus.as_ptr();
    let index = vcpu.offset_from(vcpus);
    assert!(index < core::u16::MAX as isize);
    index as u16
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_regs(vcpu: *mut VCpu) -> *mut ArchRegs {
    &mut (*vcpu).state.get_mut_unchecked().regs
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_regs_const(vcpu: *const VCpu) -> *const ArchRegs {
    &(*vcpu).state.get_mut_unchecked().regs
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_vm(vcpu: *mut VCpu) -> *mut Vm {
    (*vcpu).vm
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_cpu(vcpu: *mut VCpu) -> *mut Cpu {
    (*vcpu).state.get_mut_unchecked().cpu
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_set_cpu(vcpu: *mut VCpu, cpu: *mut Cpu) {
    (*vcpu).state.get_mut_unchecked().cpu = cpu;
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_interrupts(vcpu: *mut VCpu) -> *mut Interrupts {
    (*vcpu).interrupts.get_mut_unchecked()
}

/// Check whether the given vcpu_state is an off state, for the purpose of
/// turning vCPUs on and off. Note that aborted still counts as on in this
/// context.
#[no_mangle]
pub unsafe extern "C" fn vcpu_is_off(vcpu: VCpuExecutionLocked) -> bool {
    (*vcpu.vcpu).state.get_mut_unchecked().is_off()
}

/// Starts a vCPU of a secondary VM.
///
/// Returns true if the secondary was reset and started, or false if it was
/// already on and so nothing was done.
#[no_mangle]
pub unsafe extern "C" fn vcpu_secondary_reset_and_start(
    vcpu: *mut VCpu,
    entry: ipaddr_t,
    arg: uintreg_t,
) -> bool {
    let vm = &*(*vcpu).vm;

    assert!(vm.id != HF_PRIMARY_VM_ID);

    let mut state = (*vcpu).state.lock();
    let vcpu_was_off = state.is_off();
    if vcpu_was_off {
        // Set vCPU registers to a clean state ready for boot. As this
        // is a secondary which can migrate between pCPUs, the ID of the
        // vCPU is defined as the index and does not match the ID of the
        // pCPU it is running on.
        state.regs.reset(false, vm, vcpu_index(vcpu) as cpu_id_t);
        state.on(entry, arg);
    }

    vcpu_was_off
}

/// Handles a page fault. It does so by determining if it's a legitimate or
/// spurious fault, and recovering from the latter.
///
/// Returns true if the caller should resume the current vcpu, or false if its
/// VM should be aborted.
#[no_mangle]
pub unsafe extern "C" fn vcpu_handle_page_fault(
    current: *const VCpu,
    f: *const VCpuFaultInfo,
) -> bool {
    let vm = (*current).vm;
    let mask = (*f).mode | Mode::INVALID;
    let vm_inner = (*vm).inner.lock();

    // Check if this is a legitimate fault, i.e., if the page table doesn't
    // allow the access attemped by the VM.
    //
    // Otherwise, this is a spurious fault, likely because another CPU is
    // updating the page table. It is responsible for issuing global TLB
    // invalidations while holding the VM lock, so we don't need to do
    // anything else to recover from it. (Acquiring/releasing the lock
    // ensured that the invalidations have completed.)
    let resume = vm_inner
        .ptable
        .get_mode((*f).ipaddr, ipa_add((*f).ipaddr, 1))
        .map(|mode| mode & mask == (*f).mode)
        .unwrap_or(false);

    if !resume {
        dlog!(
            "Stage-2 page fault: pc=0x{}, vmid={}, vcpu={}, vaddr=0x{}, ipaddr=0x{}, mode=0x{}\n",
            (*f).pc,
            (*vm).id,
            vcpu_index(current),
            (*f).vaddr,
            (*f).ipaddr,
            (*f).mode.bits() as u32
        );
    }

    resume
}
