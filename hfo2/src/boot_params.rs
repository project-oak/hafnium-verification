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

#[derive(Clone)]
#[repr(C)]
pub struct MemRange {
    pub begin: paddr_t,
    pub end: paddr_t,
}

/// TODO(HfO2): Is it more natural for `paddr_t` to have 0 as default value?
impl Default for MemRange {
    fn default() -> Self {
        Self {
            begin: pa_init(0),
            end: pa_init(0),
        }
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
            reserved_ranges: Default::default(),
            reserved_ranges_count: 0,
            initrd_begin,
            initrd_end,
        }
    }
}

extern "C" {
    fn plat_get_boot_params(
        stage1_locked: mm_stage1_locked,
        p: *mut BootParams,
        ppool: *mut MPool,
    ) -> bool;

    fn plat_update_boot_params(
        stage1_locked: mm_stage1_locked,
        p: *mut BootParamsUpdate,
        ppool: *mut MPool,
    ) -> bool;
}

pub fn get(
    ptable: &mut SpinLockGuard<PageTable<Stage1>>,
    ppool: &mut MPool,
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

pub fn update(
    ptable: &mut SpinLockGuard<PageTable<Stage1>>,
    p: &mut BootParamsUpdate,
    ppool: &mut MPool,
) -> bool {
    unsafe { plat_update_boot_params(mm_stage1_locked::from_ref(ptable), p, ppool) }
}
