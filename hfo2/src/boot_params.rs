/*
 * Copyright 2019 Sanguk Park
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

use core::mem::MaybeUninit;

use crate::addr::*;
use crate::arch::*;
use crate::mm::*;
use crate::mpool::*;
use crate::spinlock::*;
use crate::types::*;

pub const MAX_MEM_RANGES: usize = 20;

#[derive(Clone, Copy)]
#[repr(C)]
pub struct MemRange {
    pub begin: paddr_t,
    pub end: paddr_t,
}

impl MemRange {
    pub fn new(begin: paddr_t, end: paddr_t) -> Self {
        Self { begin, end }
    }
}

#[repr(C)]
pub struct BootParams {
    pub cpu_ids: [cpu_id_t; MAX_CPUS],
    pub cpu_count: usize,
    pub mem_ranges: [MemRange; MAX_MEM_RANGES],
    pub mem_ranges_count: usize,
    pub initrd_begin: paddr_t,
    pub initrd_end: paddr_t,
    pub kernel_arg: uintreg_t,
}

#[repr(C)]
pub struct BootParamsUpdate {
    pub reserved_ranges: [MemRange; MAX_MEM_RANGES],
    pub reserved_ranges_count: usize,
    pub initrd_begin: paddr_t,
    pub initrd_end: paddr_t,
}

impl BootParamsUpdate {
    pub fn new(initrd_begin: paddr_t, initrd_end: paddr_t) -> Self {
        Self {
            reserved_ranges: [MemRange::new(pa_init(0), pa_init(0)); MAX_MEM_RANGES],
            reserved_ranges_count: 0,
            initrd_begin,
            initrd_end,
        }
    }
}

/// TODO(HfO2): `plat.c`, containing those functions are not ported into Rust.
/// It's because functions in `plat.c` are denoted by `#pragma weak` which is
/// not supported in Rust yet. (#47.)
extern "C" {
    fn plat_get_boot_params(
        stage1_locked: mm_stage1_locked,
        p: *mut BootParams,
        ppool: *const MPool,
    ) -> bool;

    fn plat_update_boot_params(
        stage1_locked: mm_stage1_locked,
        p: *mut BootParamsUpdate,
        ppool: *const MPool,
    ) -> bool;
}

/// Reads platform-specific boot parameters.
pub fn boot_params_get(
    ptable: &mut SpinLockGuard<PageTable<Stage1>>,
    ppool: &MPool,
) -> Option<BootParams> {
    unsafe {
        let mut p: MaybeUninit<BootParams> = MaybeUninit::uninit();

        if plat_get_boot_params(mm_stage1_locked::from_ref(ptable), p.get_mut(), ppool) {
            Some(p.assume_init())
        } else {
            None
        }
    }
}

/// Updates boot parameters for primary VM to read.
pub fn boot_params_update(
    ptable: &mut SpinLockGuard<PageTable<Stage1>>,
    p: &mut BootParamsUpdate,
    ppool: &MPool,
) -> Result<(), ()> {
    if unsafe { plat_update_boot_params(mm_stage1_locked::from_ref(ptable), p, ppool) } {
        Ok(())
    } else {
        Err(())
    }
}
