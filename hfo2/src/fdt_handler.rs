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

use core::mem;
use core::ptr::{self, NonNull};

use crate::addr::*;
use crate::arch::*;
use crate::boot_params::*;
use crate::fdt::*;
use crate::layout::*;
use crate::mm::*;
use crate::mpool::*;
use crate::page::*;
use crate::std::*;
use crate::types::*;

use scopeguard::{guard, ScopeGuard};

unsafe fn convert_number(data: *const u8, size: u32) -> u64 {
    match size {
        4 => u32::from_be(*(data as usize as *const u32)) as u64,
        8 => u64::from_be(*(data as usize as *const u64)),
        _ => 0,
    }
}

impl FdtNode {
    unsafe fn read_number(&mut self, name: *const u8) -> Result<u64, ()> {
        let (data, size) = self.read_property(name)?;

        match size {
            4 | 8 => Ok(convert_number(data, size)),
            _ => Err(()),
        }
    }

    unsafe fn write_number(&mut self, name: *const u8, value: u64) -> Result<(), ()> {
        let (data, size) = self.read_property(name)?;

        match size {
            4 => {
                *(data as *mut u32) = u32::from_be(value as u32);
            }
            8 => {
                *(data as *mut u64) = u64::from_be(value);
            }
            _ => return Err(()),
        }

        Ok(())
    }

    /// Finds the memory region where initrd is stored, and updates the fdt node
    /// cursor to the node called "chosen".
    unsafe fn find_initrd(&mut self, begin: &mut paddr_t, end: &mut paddr_t) -> bool {
        if self.find_child("chosen\0".as_ptr()).is_none() {
            dlog!("Unable to find 'chosen'\n");
            return false;
        }

        let initrd_begin = match self.read_number("linux,initrd-start\0".as_ptr()) {
            Ok(initrd_begin) => initrd_begin,
            Err(_) => {
                dlog!("Unable to read linux,initrd-start\n");
                return false;
            }
        };

        let initrd_end = match self.read_number("linux,initrd-end\0".as_ptr()) {
            Ok(initrd_end) => initrd_end,
            Err(_) => {
                dlog!("Unable to read linux,initrd-end\n");
                return false;
            }
        };

        *begin = pa_init(initrd_begin as usize);
        *end = pa_init(initrd_end as usize);

        true
    }

    pub unsafe fn find_cpus(&self, cpu_ids: *mut cpu_id_t, cpu_count: &mut usize) -> Option<()> {
        let mut node = self.clone();
        *cpu_count = 0;

        node.find_child("cpus\0".as_ptr()).or_else(|| {
            dlog!("Unable to find 'cpus'\n");
            None
        })?;

        let address_size = node
            .read_number("#address-cells\0".as_ptr())
            .map(|size| size as usize * mem::size_of::<u32>())
            .unwrap_or(mem::size_of::<u32>());

        node.first_child()?;

        // TODO(HfO2): this loop was do-while in C. Make an interator for this.
        loop {
            if node
                .read_property("device_type\0".as_ptr())
                .ok()
                .filter(|(_, size)| *size == "cpu\0".len() as u32)
                .filter(|(data, _)| {
                    memcmp_rs(
                        *data as usize as *const _,
                        "cpu\0".as_ptr() as usize as *const _,
                        "cpu\0".len(),
                    ) == 0
                })
                .is_none()
            {
                if node.next_sibling().is_none() {
                    break;
                } else {
                    continue;
                }
            }

            let (mut data, mut size) =
                if let Ok((data, size)) = node.read_property("reg\0".as_ptr()) {
                    (data, size)
                } else {
                    if node.next_sibling().is_none() {
                        break;
                    } else {
                        continue;
                    }
                };

            // Get all entries for this CPU.
            while size as usize >= address_size {
                if *cpu_count >= MAX_CPUS {
                    dlog!("Found more than {} CPUs\n", MAX_CPUS);
                    return None;
                }

                *cpu_ids.add(*cpu_count) = convert_number(data, address_size as u32) as cpu_id_t;
                *cpu_count += 1;

                size -= address_size as u32;
                data = data.add(address_size);
            }

            if node.next_sibling().is_none() {
                break;
            }
        }

        Some(())
    }

    pub unsafe fn find_memory_ranges(&self, p: &mut BootParams) -> Option<()> {
        let mut node = self.clone();

        // Get the sizes of memory range addresses and sizes.
        let address_size = node
            .read_number("#address-cells\0".as_ptr())
            .map(|size| size as usize * mem::size_of::<u32>())
            .unwrap_or(mem::size_of::<u32>());

        let size_size = node
            .read_number("#size-cells\0".as_ptr())
            .map(|size| size as usize * mem::size_of::<u32>())
            .unwrap_or(mem::size_of::<u32>());

        let entry_size = address_size + size_size;

        // Look for nodes with the device_type set to "memory".
        node.first_child()?;
        let mut mem_range_index = 0;

        // TODO(HfO2): this loop was do-while in C. Make an interator for this.
        loop {
            if node
                .read_property("device_type\0".as_ptr())
                .ok()
                .filter(|(_, size)| *size as usize == "memory\0".len())
                .filter(|(data, _)| {
                    memcmp_rs(
                        *data as usize as *const _,
                        "memory\0".as_ptr() as usize as *const _,
                        "memory\0".len(),
                    ) == 0
                })
                .is_none()
            {
                if node.next_sibling().is_none() {
                    break;
                } else {
                    continue;
                }
            }
            let (mut data, mut size) =
                if let Ok((data, size)) = node.read_property("reg\0".as_ptr()) {
                    (data, size)
                } else {
                    if node.next_sibling().is_none() {
                        break;
                    } else {
                        continue;
                    }
                };

            // Traverse all memory ranges within this node.
            while size as usize >= entry_size {
                let addr = convert_number(data, address_size as u32) as usize;
                let len = convert_number(data.add(address_size), size_size as u32) as usize;

                if mem_range_index < MAX_MEM_RANGES {
                    p.mem_ranges[mem_range_index].begin = pa_init(addr);
                    p.mem_ranges[mem_range_index].end = pa_init(addr + len);

                    mem_range_index += 1;
                } else {
                    dlog!("Found memory range {} in FDT but only {} supported, ignoring additional range of size {}.\n", mem_range_index, MAX_MEM_RANGES, len);
                }

                size -= entry_size as u32;
                data = data.add(entry_size);
            }

            if node.next_sibling().is_none() {
                break;
            }
        }

        p.mem_ranges_count = mem_range_index;
        Some(())
    }
}

pub unsafe fn map(
    stage1_ptable: &mut PageTable<Stage1>,
    fdt_addr: paddr_t,
    node: &mut FdtNode,
    ppool: &mut MPool,
) -> Option<NonNull<FdtHeader>> {
    if stage1_ptable
        .identity_map(
            fdt_addr,
            pa_add(fdt_addr, mem::size_of::<FdtHeader>()),
            Mode::R,
            ppool,
        )
        .is_err()
    {
        dlog!("Unable to map FDT header.\n");
        return None;
    }

    let mut stage1_ptable = guard(stage1_ptable, |ptable| {
        let _ = ptable.unmap(
            fdt_addr,
            pa_add(fdt_addr, mem::size_of::<FdtHeader>()),
            ppool,
        );
    });

    let fdt = pa_addr(fdt_addr) as *mut FdtHeader;

    if let Some(root) = FdtNode::new_root(&*fdt) {
        *node = root;
    } else {
        dlog!("FDT failed validation.\n");
        return None;
    }

    // Map the rest of the fdt in.
    if stage1_ptable
        .identity_map(
            fdt_addr,
            pa_add(fdt_addr, (*fdt).total_size() as usize),
            Mode::R,
            ppool,
        )
        .is_err()
    {
        dlog!("Unable to map full FDT.\n");
        return None;
    }

    mem::forget(stage1_ptable);
    NonNull::new(fdt)
}

pub unsafe fn unmap(
    stage1_ptable: &mut PageTable<Stage1>,
    fdt: *mut FdtHeader,
    ppool: &mut MPool,
) -> Result<(), ()> {
    let fdt_addr = pa_from_va(va_from_ptr(fdt as usize as *const _));

    stage1_ptable.unmap(
        fdt_addr,
        pa_add(fdt_addr, (*fdt).total_size() as usize),
        ppool,
    )
}

pub unsafe fn patch(
    stage1_ptable: &mut PageTable<Stage1>,
    fdt_addr: paddr_t,
    p: &BootParamsUpdate,
    ppool: &mut MPool,
) -> Result<(), ()> {
    // Map the fdt header in.
    if stage1_ptable
        .identity_map(
            fdt_addr,
            pa_add(fdt_addr, mem::size_of::<FdtHeader>()),
            Mode::R,
            ppool,
        )
        .is_err()
    {
        dlog!("Unable to map FDT header.\n");
        return Err(());
    }

    let mut stage1_ptable = guard(stage1_ptable, |ptable| {
        let _ = ptable.unmap(
            fdt_addr,
            pa_add(fdt_addr, mem::size_of::<FdtHeader>()),
            ppool,
        );
    });

    let fdt = pa_addr(fdt_addr) as *mut FdtHeader;

    let mut node = FdtNode::new_root(&*fdt)
        .or_else(|| {
            dlog!("FDT failed validation.\n");
            None
        })
        .ok_or(())?;
    let total_size = (*fdt).total_size();

    // Map the fdt (+ a page) in r/w mode in preparation for updating it.
    if stage1_ptable
        .identity_map(
            fdt_addr,
            pa_add(fdt_addr, total_size as usize + PAGE_SIZE),
            Mode::R | Mode::W,
            ppool,
        )
        .is_err()
    {
        dlog!("Unable to map FDT in r/w mode.\n");
        return Err(());
    }

    let stage1_ptable = guard(ScopeGuard::into_inner(stage1_ptable), |ptable| {
        if ptable
            .unmap(
                fdt_addr,
                pa_add(fdt_addr, total_size as usize + PAGE_SIZE),
                ppool,
            )
            .is_err()
        {
            dlog!("Unable to unmap writable FDT.\n");
        }
    });

    if node.find_child("\0".as_ptr()).is_none() {
        dlog!("Unable to find FDT root node.\n");
        return Err(());
    }

    if node.find_child("chosen\0".as_ptr()).is_none() {
        dlog!("Unable to find 'chosen'\n");
        return Err(());
    }

    // Patch FDT to point to new ramdisk.
    if node
        .write_number(
            "linux,initrd-start\0".as_ptr(),
            pa_addr(p.initrd_begin) as u64,
        )
        .is_err()
    {
        dlog!("Unable to write linux,initrd-start\n");
        return Err(());
    }

    if node
        .write_number("linux,initrd-end\0".as_ptr(), pa_addr(p.initrd_end) as u64)
        .is_err()
    {
        dlog!("Unable to write linux,initrd-end\n");
        return Err(());
    }

    // Patch FDT to reserve hypervisor memory so the primary VM doesn't try to
    // use it.
    (*fdt).add_mem_reservation(
        pa_addr(layout_text_begin()) as u64,
        pa_difference(layout_text_begin(), layout_text_end()) as u64,
    );
    (*fdt).add_mem_reservation(
        pa_addr(layout_rodata_begin()) as u64,
        pa_difference(layout_rodata_begin(), layout_rodata_end()) as u64,
    );
    (*fdt).add_mem_reservation(
        pa_addr(layout_data_begin()) as u64,
        pa_difference(layout_data_begin(), layout_data_end()) as u64,
    );

    // Patch FDT to reserve memory for secondary VMs.
    for i in 0..p.reserved_ranges_count {
        (*fdt).add_mem_reservation(
            pa_addr(p.reserved_ranges[i].begin) as u64,
            pa_addr(p.reserved_ranges[i].end) as u64 - pa_addr(p.reserved_ranges[i].begin) as u64,
        );
    }

    let stage1_ptable = ScopeGuard::into_inner(stage1_ptable);
    if stage1_ptable
        .unmap(
            fdt_addr,
            pa_add(fdt_addr, (*fdt).total_size() as usize + PAGE_SIZE),
            ppool,
        )
        .is_err()
    {
        dlog!("Unable to unmap writable FDT.\n");
        return Err(());
    }

    Ok(())
}

#[no_mangle]
pub unsafe extern "C" fn fdt_map(
    mut stage1_locked: mm_stage1_locked,
    fdt_addr: paddr_t,
    n: *mut FdtNode,
    ppool: *mut MPool,
) -> *mut FdtHeader {
    match map(&mut stage1_locked, fdt_addr, &mut *n, &mut *ppool) {
        Some(ret) => ret.as_ptr(),
        None => ptr::null_mut(),
    }
}

#[no_mangle]
pub unsafe extern "C" fn fdt_unmap(
    mut stage1_locked: mm_stage1_locked,
    fdt: *mut FdtHeader,
    ppool: *mut MPool,
) -> bool {
    unmap(&mut stage1_locked, &mut *fdt, &mut *ppool).is_ok()
}

#[no_mangle]
pub unsafe extern "C" fn fdt_find_cpus(
    root: *const FdtNode,
    cpu_ids: *mut cpu_id_t,
    cpu_count: *mut usize,
) {
    (*root).find_cpus(cpu_ids, &mut *cpu_count);
}

#[no_mangle]
pub unsafe extern "C" fn fdt_find_memory_ranges(root: *const FdtNode, p: *mut BootParams) {
    (*root).find_memory_ranges(&mut *p);
}

#[no_mangle]
pub unsafe extern "C" fn fdt_find_initrd(
    n: *mut FdtNode,
    begin: *mut paddr_t,
    end: *mut paddr_t,
) -> bool {
    (*n).find_initrd(&mut *begin, &mut *end)
}

#[no_mangle]
pub unsafe extern "C" fn fdt_patch(
    mut stage1_locked: mm_stage1_locked,
    fdt_addr: paddr_t,
    p: *const BootParamsUpdate,
    ppool: *mut MPool,
) -> bool {
    patch(&mut stage1_locked, fdt_addr, &*p, &mut *ppool).is_ok()
}
