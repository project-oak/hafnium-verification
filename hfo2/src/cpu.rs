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
    pub fn arch_regs_set_retval(r: *mut ArchRegs, v: uintreg_t);
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

#[repr(C)]
pub struct VCpuFaultInfo {
    ipaddr: ipaddr_t,
    vaddr: vaddr_t,
    pc: vaddr_t,
    mode: Mode,
}

#[repr(C)]
pub struct VCpu {
    /// Protects accesses to vCPU's state and architecture registers. If a
    /// vCPU is running, its execution lock is logically held by the
    /// running pCPU.
    pub execution_lock: RawSpinLock,

    /// Protects accesses to vCPU's interrupts.
    pub interrupts_lock: RawSpinLock,

    /// The state is only changed in the context of the vCPU being run. This ensures the scheduler
    /// can easily keep track of the vCPU state as transitions are indicated by the return code from
    /// the run call.
    pub state: VCpuStatus,

    pub cpu: *mut Cpu,
    pub vm: *mut Vm,
    pub regs: ArchRegs,
    pub interrupts: Interrupts,
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
        let mut vcpu_execution_locked = vcpu_lock(vcpu);

        vcpu_on(vcpu_execution_locked, entry, arg);
        vcpu_unlock(&mut vcpu_execution_locked);
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
    sl_lock(&(*vcpu).execution_lock);

    VCpuExecutionLocked { vcpu }
}

/// Tries to lock the given vCPU, and updates `locked` if succeed.
#[no_mangle]
pub unsafe extern "C" fn vcpu_try_lock(vcpu: *mut VCpu, locked: *mut VCpuExecutionLocked) -> bool {
    if sl_try_lock(&(*vcpu).execution_lock) {
        *locked = VCpuExecutionLocked { vcpu };
        true
    } else {
        false
    }
}

/// Unlocks a vCPU previously locked with vcpu_lock, and updates `locked` to
/// reflect the fact that the vCPU is no longer locked.
#[no_mangle]
pub unsafe extern "C" fn vcpu_unlock(locked: *mut VCpuExecutionLocked) {
    sl_unlock(&(*(*locked).vcpu).execution_lock);
    (*locked).vcpu = ptr::null_mut();
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_init(vcpu: *mut VCpu, vm: *mut Vm) {
    memset_s(vcpu as _, mem::size_of::<VCpu>(), 0, mem::size_of::<VCpu>());
    sl_init(&mut (*vcpu).execution_lock);
    sl_init(&mut (*vcpu).interrupts_lock);
    (*vcpu).vm = vm;
    (*vcpu).state = VCpuStatus::Off;
}

/// Initialise the registers for the given vCPU and set the state to
/// VCpuStatus::Ready. The caller must hold the vCPU execution lock while
/// calling this.
#[no_mangle]
pub unsafe extern "C" fn vcpu_on(vcpu: VCpuExecutionLocked, entry: ipaddr_t, arg: uintreg_t) {
    arch_regs_set_pc_arg(&mut (*vcpu.vcpu).regs, entry, arg);
    (*vcpu.vcpu).state = VCpuStatus::Ready;
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
    &mut (*vcpu).regs
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_regs_const(vcpu: *const VCpu) -> *const ArchRegs {
    &(*vcpu).regs
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_vm(vcpu: *mut VCpu) -> *mut Vm {
    (*vcpu).vm
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_cpu(vcpu: *mut VCpu) -> *mut Cpu {
    (*vcpu).cpu
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_set_cpu(vcpu: *mut VCpu, cpu: *mut Cpu) {
    (*vcpu).cpu = cpu;
}

#[no_mangle]
pub unsafe extern "C" fn vcpu_get_interrupts(vcpu: *mut VCpu) -> *mut Interrupts {
    &mut (*vcpu).interrupts
}

/// Check whether the given vcpu_state is an off state, for the purpose of
/// turning vCPUs on and off. Note that aborted still counts as on in this
/// context.
#[no_mangle]
pub unsafe extern "C" fn vcpu_is_off(vcpu: VCpuExecutionLocked) -> bool {
    match (*vcpu.vcpu).state {
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
    let mut vcpu_execution_locked;
    let vm = (*vcpu).vm;
    let vcpu_was_off;

    assert!((*vm).id != HF_PRIMARY_VM_ID);

    vcpu_execution_locked = vcpu_lock(vcpu);
    vcpu_was_off = vcpu_is_off(vcpu_execution_locked);
    if vcpu_was_off {
        // Set vCPU registers to a clean state ready for boot. As this
        // is a secondary which can migrate between pCPUs, the ID of the
        // vCPU is defined as the index and does not match the ID of the
        // pCPU it is running on.
        arch_regs_reset(
            &mut (*vcpu).regs,
            false,
            (*vm).id,
            vcpu_index(vcpu) as cpu_id_t,
            (*vm).get_ptable_raw(),
        );
        vcpu_on(vcpu_execution_locked, entry, arg);
    }

    vcpu_unlock(&mut vcpu_execution_locked);
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
