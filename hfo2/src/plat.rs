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

use crate::boot_params::*;
use crate::mm::*;
use crate::mpool::*;
use crate::addr::*;
use crate::layout::*;
use crate::arch::*;
use crate::fdt::*;

/// Default implementation assumes the FDT has been linked into the image.
///
/// This can be overridden e.g. to provide a fixed address or an address passed
/// by the loader.
fn plat_get_fdt_addr() -> paddr_t {
    unsafe { layout_fdt_begin() }
}

/// Default implementation assumes the initrd has been linked into the image.
///
/// This can be overridden e.g. to provide a fixed address or an address passed
/// by the loader.
fn plat_get_initrd_range(stage1_locked: mm_stage1_locked,
    begin: &mut paddr_t, end: &mut paddr_t, ppool: &mut MPool) {
    *begin = unsafe { layout_initrd_begin() };
    *end = unsafe { layout_initrd_end() };
}

/// Default implementation assumes the FDT address is passed to the kernel.
///
/// TODO: make this part of the VM configuration as secondary VMs will also need
/// to take arguments.
fn plat_get_kernel_arg() -> uintreg_t {
    pa_addr(plat_get_fdt_addr()) as uintreg_t
}


/// Default implementation extracts the boot parameters from the FDT but the
/// initrd is provided separately.
#[no_mangle]
pub unsafe extern "C" fn plat_get_boot_params(
    stage1_locked: mm_stage1_locked,
    p: &mut BootParams,
    ppool: &mut MPool,
) -> bool {
    let mut ret = false;
    let n;

    plat_get_initrd_range(stage1_locked, &mut p.initrd_begin, &mut p.initrd_end, ppool);
    p.kernel_arg = plat_get_kernel_arg();

    // Get the memory map from the FDT.
    let fdt = fdt_map(stage1_locked, plat_get_fdt_addr(), &n, ppool);
    if fdt.is_null() {
        return false;
    }

    if !fdt_find_child(&n, "") {
        dlog!("Unable to find FDT root node.\n");
        // goto out_unmap_fdt;
        if !fdt_unmap(stage1_locked, fdt, ppool) {
            dlog!("Unable to unmap fdt.");
            return false;
        }

        return ret;
    }

    fdt_find_cpus(&n, p.cpu_ids, p.cpu_count);

    p.mem_ranges_count = 0;
    fdt_find_memory_ranges(&n, p);

    ret = true;

    // out_unmap_fdt:
    if !fdt_unmap(stage1_locked, fdt, ppool) {
        dlog!("Unable to unmap fdt.");
        return false;
    }

    return ret;
}

/// Default implementation updates the FDT which is the argument passed to the
/// primary VM's kernel.
///
/// TODO: in future, each VM will declare whether it expects an argument passed
/// and that will be static data e.g. it will provide its own FDT so there will
/// be no FDT modification. This is done because each VM has a very different
/// view of the system and we don't want to force VMs to require loader code 
/// when another loader can load the data for it.
pub fn plat_update_boot_params(
    stage1_locked: mm_stage1_locked,
    p: &mut BootParamsUpdate,
    ppool: &mut MPool,
) -> bool {
    fdt_patch(stage1_locked, plat_get_fdt_addr(), p, ppool);
}
