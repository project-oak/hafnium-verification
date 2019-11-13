/*
 * Copyright 2019 Sanguk Park.
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

// TODO: Refactor type names and remove this.
#![allow(non_camel_case_types)]

use core::mem;

use crate::cpu::*;
use crate::types::*;

const FLOAT_REG_BYTES: usize = 16;

/// The ID of a physical or virtual CPU.
pub type cpu_id_t = u64;

/// The integer type corresponding to the native register size.
pub type uintreg_t = u64;

/// Integer type large enough to hold a physical address.
pub type uintpaddr_t = uintptr_t;

/// Integer type large enough to hold a virtual address.
pub type uintvaddr_t = uintptr_t;

/// The type of a page table entry (PTE).
pub type pte_t = u64;

/// The struct for storing a floating point register.
///
/// 2 64-bit integers used to avoid need for FP support at this level.
#[repr(C, align(16))]
struct float_reg {
    // TODO: alignas(FLOAT_REG_BYTES)
    low: u64,
    high: u64,
}

const_assert_eq!(float_reg_size; mem::size_of::<float_reg>(), FLOAT_REG_BYTES);

/// Arch-specific information about a VM.
#[repr(C)]
pub struct ArchVm {
    /// The index of the last vCPU of this VM which ran on each pCPU. Each
    /// element of this array should only be read or written by code running
    /// on that CPU, which avoids contention and so no lock is needed to
    /// access this field.
    last_vcpu_on_cpu: [spci_vcpu_index_t; MAX_CPUS],
}

/// Type to represent the register state of a vCPU.
#[repr(C)]
pub struct ArchRegs {
    /// General purpose registers.
    r: [uintreg_t; 31],
    pc: uintreg_t,
    spsr: uintreg_t,

    /// System registers.
    lazy: ArchSysRegs,

    // Floating point registers.
    fp: [float_reg; 32],
    fpsr: uintreg_t,
    fpcr: uintreg_t,

    // TODO: 'hikey' environment has GIC version 2.
    //#[cfg(any(feature = "GIC_VERSION=3", feature = "GIC_VERSION=4"))]
    gic_ich_hcr_el2: uintreg_t,

    /// Peripheral registers, handled separately from other system registers.
    peripherals: ArchPeriRegs,
}

// from src/arch/aarch64/hypervisor/offset.h
// Note: always keep this constants same as ones in offset.h
const CPU_ID: usize = 0;
const CPU_STACK_BOTTOM: usize = 8;
const VCPU_REGS: usize = 32;
const REGS_LAZY: usize = 264;
const REGS_FREGS: usize = REGS_LAZY + 232;
//#[cfg(any(feature = "GIC_VERSION=3", feature = "GIC_VERSION=4"))]
const REGS_GIC: usize = REGS_FREGS + 528;

/// Checks above constants are correct.
/// HfO2: This checking was originally done in compile time in C. But it was
/// impossible because Rust compiler rejects construction of variables with
/// interior mutability (`VCpu` has `SpinLock`) in constant expressions. Hence
/// we check those constants in runtime.
pub fn arch_cpu_module_init() {
    assert_eq!(offset_of!(Cpu, id), CPU_ID);
    assert_eq!(offset_of!(Cpu, stack_bottom), CPU_STACK_BOTTOM);
    // assert_eq!(
    //     offset_of!(VCpu, inner)
    //     + 8 // expected value of offset_of!(SpinLock<VCpuState>, data), but it
    //         // is not working. see Gilnaa/memoffset#21.
    //     + offset_of!(VCpuInner, regs),
    //     VCPU_REGS
    // );
    assert_eq!(offset_of!(ArchRegs, lazy), REGS_LAZY);
    assert_eq!(offset_of!(ArchRegs, fp), REGS_FREGS);
    assert_eq!(offset_of!(ArchRegs, gic_ich_hcr_el2), REGS_GIC);
}

#[repr(C)]
pub struct ArchSysRegs {
    vmpidr_el2: uintreg_t,
    csselr_el1: uintreg_t,
    sctlr_el1: uintreg_t,
    actlr_el1: uintreg_t,
    cpacr_el1: uintreg_t,
    ttbr0_el1: uintreg_t,
    ttbr1_el1: uintreg_t,
    tcr_el1: uintreg_t,
    esr_el1: uintreg_t,
    afsr0_el1: uintreg_t,
    afsr1_el1: uintreg_t,
    far_el1: uintreg_t,
    mair_el1: uintreg_t,
    vbar_el1: uintreg_t,
    contextidr_el1: uintreg_t,
    tpidr_el0: uintreg_t,
    tpidrro_el0: uintreg_t,
    tpidr_el1: uintreg_t,
    amair_el1: uintreg_t,
    cntkctl_el1: uintreg_t,
    sp_el0: uintreg_t,
    sp_el1: uintreg_t,
    elr_el1: uintreg_t,
    spsr_el1: uintreg_t,
    par_el1: uintreg_t,
    hcr_el2: uintreg_t,
    cptr_el2: uintreg_t,
    cnthctl_el2: uintreg_t,
    vttbr_el2: uintreg_t,
}

#[repr(C)]
struct ArchPeriRegs {
    cntv_cval_el0: uintreg_t,
    cntv_ctl_el0: uintreg_t,
}
