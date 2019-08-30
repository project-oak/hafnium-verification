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

use crate::addr::*;
use crate::arch::*;
use crate::mm::*;
use crate::mpool::*;
use crate::types::*;

pub const MAX_MEM_RANGES: usize = 20;

#[derive(Clone)]
pub struct MemRange {
    pub begin: paddr_t,
    pub end: paddr_t,
}

pub struct BootParams {
    pub cpu_ids: [cpu_id_t; MAX_CPUS],
    pub cpu_count: usize,
    pub mem_ranges: [MemRange; MAX_MEM_RANGES],
    pub mem_ranges_count: usize,
    pub initrd_begin: paddr_t,
    pub initrd_end: paddr_t,
    pub kernel_arg: uintreg_t,
}

pub struct BootParamsUpdate {
    pub reserved_ranges: [MemRange; MAX_MEM_RANGES],
    pub reserved_ranges_count: usize,
    pub initrd_begin: paddr_t,
    pub initrd_end: paddr_t,
}

extern "C" {
    pub fn plat_get_boot_params(
        stage1_locked: mm_stage1_locked,
        p: *mut BootParams,
        ppool: *mut MPool,
    ) -> bool;
    pub fn plat_update_boot_params(
        stage1_locked: mm_stage1_locked,
        p: *mut BootParamsUpdate,
        ppool: *mut MPool,
    ) -> bool;
}
