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
use crate::boot_flow::*;
use crate::fdt::*;
use crate::fdt_handler::*;
use crate::mm::*;
use crate::mpool::*;
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

impl BootParams {
    /// Extract the boot parameters from the FDT and the boot-flow driver.
    pub fn init<'a>(&mut self, fdt_root: &FdtNode<'a>) -> Result<(), ()> {
        self.mem_ranges_count = 0;
        self.kernel_arg = plat::get_kernel_arg();

        let (begin, end) = plat::get_initrd_range(fdt_root)?;
        self.initrd_begin = begin;
        self.initrd_end = end;

        self.cpu_count = fdt_root.find_cpus(&mut self.cpu_ids).ok_or(())?;
        fdt_root.find_memory_ranges(self).ok_or(())?;

        Ok(())
    }
}

/// Updates the FDT before being passed to the primary VM's kernel.
///
/// TODO: in future, each VM will declare whether it expects an argument passed and that will be
/// static data e.g. it will provide its own FDT so there will be no FDT modification. This is
/// done because each VM has a very different view of the system and we don't want to force VMs
/// to require loader code when another loader can load the data for it.
pub fn boot_params_patch_fdt(
    ptable: &mut PageTable<Stage1>,
    p: &BootParamsUpdate,
    mpool: &MPool,
) -> Result<(), ()> {
    unsafe { patch(ptable, plat::get_fdt_addr(), p, mpool) }
}
