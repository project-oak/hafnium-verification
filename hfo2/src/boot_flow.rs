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
use crate::boot_params::*;
use crate::fdt::*;
use crate::fdt_handler::*;
use crate::manifest::*;
use crate::mm::*;
use crate::mpool::*;

// from "inc/hf/plat/boot_flow.h"
extern "C" {
    fn plat_get_fdt_addr() -> paddr_t;
    fn plat_get_kernel_arg() -> uintreg_t;
    fn plat_get_initrd_range(
        fdt_root: *const fdt_node,
        begin: *mut paddr_t,
        end: *mut paddr_t,
    ) -> bool;
}

pub mod plat {
    use super::*;

    pub fn get_fdt_addr() -> paddr_t {
        unsafe { plat_get_fdt_addr() }
    }

    pub fn get_kernel_arg() -> uintreg_t {
        unsafe { plat_get_kernel_arg() }
    }

    pub fn get_initrd_range<'a>(fdt_root: &FdtNode<'a>) -> Result<(paddr_t, paddr_t), ()> {
        let fdt_root = fdt_root.clone().into();
        let (mut begin, mut end) = (pa_init(0), pa_init(0));

        if unsafe { plat_get_initrd_range(&fdt_root, &mut begin, &mut end) } {
            Ok((begin, end))
        } else {
            Err(())
        }
    }
}

/// Parse information from FDT needed to initialize Hafnium.
/// FDT is mapped at the beginning and unmapped before exiting the function.
pub fn boot_flow_init(
    ptable: &mut PageTable<Stage1>,
    manifest: &mut Manifest,
    boot_params: &mut BootParams,
    ppool: &MPool,
) -> Result<(), ()> {
    // Get the memory map from the FDT.
    let mut fdt_root = unsafe { map(ptable, plat::get_fdt_addr(), ppool) }.ok_or_else(|| {
        dlog!("Unable to map FDT.\n");
    })?;

    let ret = try {
        fdt_root.find_child("\0".as_ptr()).ok_or_else(|| {
            dlog!("Unable to find FDT root node.\n");
        })?;

        manifest.init(&fdt_root).map_err(|e| {
            dlog!(
                "Could not parse manifest: {}.\n",
                <Error as Into<&'static str>>::into(e)
            );
        })?;

        boot_params.init(&fdt_root).map_err(|_| {
            dlog!("Could not parse boot params.\n");
        })?;
    };

    unsafe { unmap(ptable, pa_addr(plat::get_fdt_addr()) as _, ppool) }.map_err(|_| {
        dlog!("Unable to unmap FDT.\n");
    })?;

    ret
}
