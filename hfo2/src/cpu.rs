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

use crate::mm::*;
use crate::page::*;
use crate::spinlock::*;
use crate::types::*;
use crate::vm::*;
use crate::arch::*;

extern "C" {
    fn arch_irq_enable();
    fn arch_irq_disable();
    pub fn vcpu_init(vcpu: *mut VCpu, vm: *mut Vm);
}

const STACK_SIZE: usize = PAGE_SIZE;

/// The number of bits in each element of the interrupt bitfields.
const INTERRUPT_REGISTER_BITS: usize = 32;

#[repr(C)]
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

#[repr(C)]
pub struct Interrupts {
    /// Bitfield keeping track of which interrupts are enabled.
    enabled: [u32; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],

    /// Bitfield keeping track of which interrupts are pending.
    pending: [u32; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],

    /// The number of interrupts which are currently both enabled and pending. i.e. the number of
    /// bits set in enabled & pending.
    enabled_and_pending_count: u32,
}

#[repr(C)]
pub struct VCpuFaultInfo {
    ipaddr: usize,
    vaddr: usize,
    pc: usize,
    mode: Mode,
}

#[repr(C)]
pub struct VCpu {
    lock: RawSpinLock,

    /// The state is only changed in the context of the vCPU being run. This ensures the scheduler
    /// can easily keep track of the vCPU state as transitions are indicated by the return code from
    /// the run call.
    state: VCpuStatus,

    cpu: *mut Cpu, 
    vm: *mut Vm,
    regs: ArchRegs,
    interrupts: Interrupts,

    /// Determine whether the 'regs' field is available for use. This is set
    /// to false when a vCPU is about to run on a physical CPU, and is set
    /// back to true when it is descheduled.
    regs_available: bool,
}

// TODO: Update alignment such that cpus are in different cache lines.
#[repr(C)]
pub struct Cpu {
    /// CPU identifier. Doesn't have to be contiguous.
    id: cpu_id_t,

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
