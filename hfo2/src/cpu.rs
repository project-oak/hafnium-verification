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

use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::Deref;
use core::ptr;

use crate::addr::*;
use crate::arch::*;
use crate::mm::*;
use crate::page::*;
use crate::singleton::*;
use crate::spinlock::*;
use crate::std::*;
use crate::types::*;
use crate::vm::*;

use arrayvec::ArrayVec;

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

pub const STACK_SIZE: usize = PAGE_SIZE;

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
    enabled: [u32; HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS],

    /// Bitfield keeping track of which interrupts are pending.
    pending: [u32; HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS],

    /// The number of interrupts which are currently both enabled and pending. i.e. the number of
    /// bits set in enabled & pending.
    enabled_and_pending_count: u32,
}

impl Interrupts {
    pub fn new() -> Self {
        Self {
            enabled: [0; HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS],
            pending: [0; HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS],
            enabled_and_pending_count: 0,
        }
    }

    pub fn id_to_index(intid: intid_t) -> Result<(usize, u32), ()> {
        if intid >= HF_NUM_INTIDS {
            return Err(());
        }

        let intid_index = intid as usize / INTERRUPT_REGISTER_BITS;
        let intid_mask = 1u32 << (intid % INTERRUPT_REGISTER_BITS as u32);

        Ok((intid_index, intid_mask))
    }

    /// injects a virtual interrupt of the given ID into the given target vCPU.
    /// Returns:
    ///  - None if no further action is needed.
    ///  - Some(()) if the vcpu had have no pending interrupt before, thus
    ///    proper scheduling is required.
    pub fn inject(&mut self, intid: intid_t) -> Result<(), ()> {
        let (intid_index, intid_mask) = Self::id_to_index(intid)?;

        // Make it pending.
        let pending = self.pending[intid_index];
        self.pending[intid_index] |= intid_mask;

        // We only need to change state and (maybe) trigger a virtual IRQ if it
        // is enabled and was not previously pending. Otherwise we can skip
        // everything except setting the pending bit.
        //
        // If you change this logic make sure to update the need_vm_lock logic
        // above to match.
        if self.enabled[intid_index] & !pending & intid_mask == 0 {
            return Err(());
        }

        // Increment the count.
        self.enabled_and_pending_count += 1;

        // Only need to update state if there was not already an
        // interrupt enabled and pending.
        if self.enabled_and_pending_count != 1 {
            Err(())
        } else {
            Ok(())
        }
    }

    /// Enables or disables a given interrupt ID for the calling vCPU.
    pub fn enable(&mut self, intid: intid_t, enable: bool) -> Result<(), ()> {
        let (intid_index, intid_mask) = Self::id_to_index(intid)?;

        if enable {
            // If it is pending and was not enabled before, increment the count.
            if (self.pending[intid_index] & !self.enabled[intid_index] & intid_mask) != 0 {
                self.enabled_and_pending_count += 1;
            }
            self.enabled[intid_index] |= intid_mask;
        } else {
            // If it is pending and was enabled before, decrement the count.
            if (self.pending[intid_index] & self.enabled[intid_index] & intid_mask) != 0 {
                self.enabled_and_pending_count -= 1;
            }
            self.enabled[intid_index] &= !intid_mask;
        }

        Ok(())
    }

    #[inline]
    pub fn is_interrupted(&self) -> bool {
        self.enabled_and_pending_count > 0
    }

    /// Returns the ID of the next pending interrupt for the calling vCPU, and
    /// acknowledges it (i.e. marks it as no longer pending). Returns
    /// HF_INVALID_INTID if there are no pending interrupts.
    pub fn get(&mut self) -> intid_t {
        // Find the first enabled pending interrupt ID, returns it, and
        // deactive it.
        for i in 0..(HF_NUM_INTIDS as usize / INTERRUPT_REGISTER_BITS) {
            let enabled_and_pending = self.enabled[i] & self.pending[i];
            if enabled_and_pending != 0 {
                let bit_index = enabled_and_pending.trailing_zeros();

                // Mark it as no longer pending and decrement the count.
                self.pending[i] &= !(1u32 << bit_index);
                self.enabled_and_pending_count -= 1;
                return (i * INTERRUPT_REGISTER_BITS) as u32 + bit_index;
            }
        }

        HF_INVALID_INTID
    }
}

impl ArchRegs {
    pub fn new() -> Self {
        let mut ret;
        unsafe {
            ret = MaybeUninit::uninit().assume_init();
            memset_s(
                &mut ret as *mut _ as usize as *mut _,
                mem::size_of_val(&ret),
                0,
                mem::size_of_val(&ret),
            );
        }
        ret
    }

    /// Reset the register values other than the PC and argument which are set
    /// with `arch_regs_set_pc_arg()`.
    pub fn reset(&mut self, is_primary: bool, vm: &Vm, vcpu_id: cpu_id_t) {
        unsafe { arch_regs_reset(self, is_primary, vm.id, vcpu_id, vm.get_ptable_raw()) }
    }

    /// Updates the register holding the return value of a function.
    pub fn set_retval(&mut self, v: uintreg_t) {
        unsafe { arch_regs_set_retval(self, v) }
    }

    /// Updates the given registers so that when a vcpu runs, it starts off at
    /// the given address (pc) with the given argument.
    pub fn set_pc_arg(&mut self, pc: ipaddr_t, arg: uintreg_t) {
        unsafe { arch_regs_set_pc_arg(self, pc, arg) }
    }

    pub fn timer_mask(&mut self) {
        unsafe { arch_timer_mask(self) }
    }

    pub fn timer_enabled(&self) -> bool {
        unsafe { arch_timer_enabled(self) }
    }

    pub fn timer_remaining_ns(&self) -> u64 {
        unsafe { arch_timer_remaining_ns(self) }
    }

    pub fn timer_pending(&self) -> bool {
        unsafe { arch_timer_pending(self) }
    }
}

#[repr(C)]
pub struct VCpuFaultInfo {
    ipaddr: ipaddr_t,
    vaddr: vaddr_t,
    pc: vaddr_t,
    mode: Mode,
}

pub struct VCpuInner {
    /// The state is only changed in the context of the vCPU being run. This
    /// ensures the scheduler can easily keep track of the vCPU state as
    /// transitions are indicated by the return code from the run call.
    pub state: VCpuStatus,
    pub cpu: *const Cpu,
    pub regs: ArchRegs,
}

impl VCpuInner {
    pub fn new() -> Self {
        Self {
            state: VCpuStatus::Off,
            cpu: ptr::null(),
            regs: ArchRegs::new(),
        }
    }

    /// Initialise the registers for the given vCPU and set the state to
    /// VCpuStatus::Ready. The caller must hold the vCPU execution lock while
    /// calling this.
    pub fn on(&mut self, entry: ipaddr_t, arg: uintreg_t) {
        self.regs.set_pc_arg(entry, arg);
        self.state = VCpuStatus::Ready;
    }

    /// Check whether self is an off state, for the purpose of turning vCPUs on
    /// and off. Note that aborted still counts as on in this context.
    pub fn is_off(&self) -> bool {
        // Aborted still counts as ON for the purposes of PSCI, because according to the PSCI
        // specification (section 5.7.1) a core is only considered to be off if it has been turned
        // off with a CPU_OFF call or hasn't yet been turned on with a CPU_ON call.
        self.state == VCpuStatus::Off
    }
}

#[repr(C)]
pub struct VCpu {
    pub vm: *mut Vm,

    /// If a vCPU is running, its lock is logically held by the running pCPU.
    pub inner: SpinLock<VCpuInner>,
    pub interrupts: SpinLock<Interrupts>,
}

impl VCpu {
    pub fn new(vm: *mut Vm) -> Self {
        Self {
            vm,
            inner: SpinLock::new(VCpuInner::new()),
            interrupts: SpinLock::new(Interrupts::new()),
        }
    }

    pub fn set_cpu(&mut self, cpu: *const Cpu) {
        self.inner.get_mut().cpu = cpu;
    }
}

/// Encapsulates a vCPU whose lock is held.
#[repr(C)]
pub struct VCpuExecutionLocked {
    vcpu: *const VCpu,
}

impl Drop for VCpuExecutionLocked {
    fn drop(&mut self) {
        unsafe {
            (*self.vcpu).inner.unlock_unchecked();
        }
    }
}

impl Deref for VCpuExecutionLocked {
    type Target = VCpu;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.vcpu }
    }
}

impl VCpuExecutionLocked {
    #[inline]
    pub unsafe fn from_raw(vcpu: *const VCpu) -> Self {
        Self { vcpu }
    }

    #[inline]
    pub fn into_raw(self) -> *const VCpu {
        let ret = self.vcpu;
        mem::forget(self);
        ret
    }

    #[inline]
    pub fn get_inner(&self) -> &VCpuInner {
        unsafe { (*self.vcpu).inner.get_unchecked() }
    }

    #[inline]
    pub fn get_inner_mut(&mut self) -> &mut VCpuInner {
        unsafe { (*self.vcpu).inner.get_mut_unchecked() }
    }
}

// TODO: Update alignment such that cpus are in different cache lines.
#[repr(C)]
pub struct Cpu {
    /// CPU identifier. Doesn't have to be contiguous.
    pub id: cpu_id_t,

    /// Pointer to bottom of the stack.
    /// `pub` here is only required by `arch_cpu_module_init`.
    pub stack_bottom: *mut c_void,

    /// Determines whether or not the cpu is currently on.
    is_on: SpinLock<bool>,
}

impl Cpu {
    pub fn new(id: cpu_id_t, stack_bottom: usize, is_on: bool) -> Self {
        Self {
            id,
            stack_bottom: stack_bottom as *mut _,
            is_on: SpinLock::new(is_on),
        }
    }
}

pub struct CpuManager {
    /// State of all supported CPUs.
    cpus: ArrayVec<[Cpu; MAX_CPUS]>,
}

impl CpuManager {
    pub fn new(
        cpu_ids: &[cpu_id_t],
        boot_cpu_id: cpu_id_t,
        stacks: &[[u8; STACK_SIZE]; MAX_CPUS],
    ) -> Self {
        let mut cpus: ArrayVec<[Cpu; MAX_CPUS]> = ArrayVec::new();

        // Initialize boot CPU.
        let boot_stack = stacks[0].as_ptr() as usize;
        cpus.push(Cpu::new(boot_cpu_id, boot_stack + STACK_SIZE, true));

        let cpu_ids = cpu_ids.iter().filter(|id| boot_cpu_id != **id);
        let stacks = stacks.iter().skip(1);

        for (cpu_id, stack) in cpu_ids.zip(stacks) {
            cpus.push(Cpu::new(
                *cpu_id,
                stack.as_ptr() as usize + STACK_SIZE,
                false,
            ));
        }

        Self { cpus }
    }

    pub unsafe fn index_of(&self, c: &Cpu) -> usize {
        (c as *const Cpu).offset_from(self.cpus.as_ptr()) as usize
    }

    pub unsafe fn cpu_on(&self, c: &Cpu, entry: ipaddr_t, arg: uintreg_t) -> bool {
        let mut is_on = c.is_on.lock();
        let prev = *is_on;
        *is_on = true;

        if !prev {
            let vm = vm_manager().get(HF_PRIMARY_VM_ID).unwrap();
            let vcpu = vm.vcpus.get(self.index_of(c)).unwrap();

            vcpu.inner.lock().on(entry, arg);
        }

        prev
    }

    pub fn lookup(&self, id: cpu_id_t) -> Option<&Cpu> {
        for cpu in self.cpus.iter() {
            if cpu.id == id {
                return Some(cpu);
            }
        }

        None
    }

    /// Temporal impl (WIP)
    pub fn boot_cpu(&self) -> *mut Cpu {
        self.cpus.get(0).unwrap() as &Cpu as *const _ as usize as *mut _
    }
}

#[no_mangle]
pub unsafe extern "C" fn cpu_index(c: *const Cpu) -> usize {
    cpu_manager().index_of(&*c)
}

/// Turns CPU on and returns the previous state.
#[no_mangle]
pub unsafe extern "C" fn cpu_on(c: *mut Cpu, entry: ipaddr_t, arg: uintreg_t) -> bool {
    cpu_manager().cpu_on(&*c, entry, arg)
}

/// Prepares the CPU for turning itself off.
#[no_mangle]
pub unsafe extern "C" fn cpu_off(c: *mut Cpu) {
    *((*c).is_on.lock()) = false;
}

/// Searches for a CPU based on its id.
#[no_mangle]
pub unsafe extern "C" fn cpu_find(id: cpu_id_t) -> *mut Cpu {
    cpu_manager()
        .lookup(id)
        .map(|cpu| cpu as *const _ as usize as *mut _)
        .unwrap_or(ptr::null_mut())
}

/// Locks the given vCPU and updates `locked` to hold the newly locked vCPU.
#[no_mangle]
pub unsafe extern "C" fn vcpu_lock(vcpu: *mut VCpu) -> VCpuExecutionLocked {
    mem::forget((*vcpu).inner.lock());
    VCpuExecutionLocked { vcpu }
}

/// Tries to lock the given vCPU, and updates `locked` if succeed.
#[no_mangle]
pub unsafe extern "C" fn vcpu_try_lock(vcpu: *mut VCpu, locked: *mut VCpuExecutionLocked) -> bool {
    (*vcpu)
        .inner
        .try_lock()
        .map(|guard| {
            mem::forget(guard);
            ptr::write(locked, VCpuExecutionLocked { vcpu });
        })
        .is_ok()
}

/// Unlocks a vCPU previously locked with vcpu_lock, and updates `locked` to
/// reflect the fact that the vCPU is no longer locked.
#[no_mangle]
pub unsafe extern "C" fn vcpu_unlock(locked: *mut VCpuExecutionLocked) {
    drop(ptr::read(locked));
    (*locked).vcpu = ptr::null_mut();
}

/// Initialise the registers for the given vCPU and set the state to
/// VCpuStatus::Ready. The caller must hold the vCPU execution lock while
/// calling this.
#[no_mangle]
pub unsafe extern "C" fn vcpu_on(vcpu: VCpuExecutionLocked, entry: ipaddr_t, arg: uintreg_t) {
    let mut vcpu = ManuallyDrop::new(vcpu);
    vcpu.get_inner_mut().on(entry, arg);
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
    &mut (*vcpu).inner.get_mut_unchecked().regs
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_regs_const(vcpu: *const VCpu) -> *const ArchRegs {
    &(*vcpu).inner.get_mut_unchecked().regs
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_vm(vcpu: *mut VCpu) -> *mut Vm {
    (*vcpu).vm
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_cpu(vcpu: *const VCpu) -> *mut Cpu {
    (*vcpu).inner.get_mut_unchecked().cpu as usize as *mut _
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_interrupts(vcpu: *mut VCpu) -> *mut Interrupts {
    (*vcpu).interrupts.get_mut_unchecked()
}

/// Check whether the given vcpu_inner is an off state, for the purpose of
/// turning vCPUs on and off. Note that aborted still counts as on in this
/// context.
#[no_mangle]
pub unsafe extern "C" fn vcpu_is_off(vcpu: VCpuExecutionLocked) -> bool {
    let vcpu = ManuallyDrop::new(vcpu);
    vcpu.get_inner().is_off()
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

    let mut state = (*vcpu).inner.lock();
    let vcpu_was_off = state.is_off();
    if vcpu_was_off {
        // Set vCPU registers to a clean state ready for boot. As this
        // is a secondary which can migrate between pCPUs, the ID of the
        // vCPU is defined as the index and does not match the ID of the
        // pCPU it is running on.
        state
            .regs
            .reset(false, vm, cpu_id_t::from(vcpu_index(vcpu)));
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
