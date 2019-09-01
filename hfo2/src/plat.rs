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

//! TODO(HfO2): Functions here were denoted by `#pragma weak`, but no other
//! definitions are in Hafnium C code. How can I denote this?

use core::mem;

use crate::addr::*;
use crate::arch::*;
use crate::boot_params::*;
use crate::fdt_handler;
use crate::layout::*;
use crate::mm::*;
use crate::mpool::*;

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
fn plat_get_initrd_range(begin: &mut paddr_t, end: &mut paddr_t) {
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
pub unsafe extern "C" fn plat_get_boot_params(
    ptable: &mut PageTable<Stage1>,
    p: &mut BootParams,
    ppool: &mut MPool,
) -> bool {
    let mut ret = false;
    let mut n = mem::uninitialized();

    plat_get_initrd_range(&mut p.initrd_begin, &mut p.initrd_end);
    p.kernel_arg = plat_get_kernel_arg();

    // Get the memory map from the FDT.
    let fdt = fdt_handler::map(ptable, plat_get_fdt_addr(), &mut n, ppool);
    if fdt.is_none() {
        return false;
    }
    let fdt = fdt.unwrap().as_ptr();

    if n.find_child("\0".as_ptr()).is_none() {
        dlog!("Unable to find FDT root node.\n");
        // goto out_unmap_fdt;
        if fdt_handler::unmap(ptable, fdt, ppool).is_err() {
            dlog!("Unable to unmap fdt.");
            return false;
        }

        return ret;
    }

    n.find_cpus(p.cpu_ids.as_mut_ptr(), &mut p.cpu_count);

    p.mem_ranges_count = 0;
    n.find_memory_ranges(p);

    ret = true;

    // out_unmap_fdt:
    if fdt_handler::unmap(ptable, fdt, ppool).is_err() {
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
pub unsafe fn plat_update_boot_params(
    ptable: &mut PageTable<Stage1>,
    p: &mut BootParamsUpdate,
    ppool: &mut MPool,
) -> bool {
    fdt_handler::patch(ptable, plat_get_fdt_addr(), p, ppool).is_ok()
}
