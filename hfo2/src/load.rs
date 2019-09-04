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

use core::mem::{self, MaybeUninit};
use core::ptr;
use core::slice;

use crate::addr::*;
use crate::arch::*;
use crate::boot_params::*;
use crate::cpio::*;
use crate::cpu::*;
use crate::layout::*;
use crate::memiter::*;
use crate::mm::*;
use crate::mpool::*;
use crate::page::*;
use crate::std::*;
use crate::types::*;
use crate::utils::*;
use crate::vm::*;

/// Copies data to an unmapped location by mapping it for write, copying the
/// data, then unmapping it.
///
/// The data is written so that it is available to all cores with the cache
/// disabled. When switching to the partitions, the caching is initially
/// disabled so the data must be available without the cache.
unsafe fn copy_to_unmapped(
    hypervisor_ptable: &mut PageTable<Stage1>,
    to: paddr_t,
    from: *const c_void,
    size: usize,
    ppool: &mut MPool,
) -> bool {
    let to_end = pa_add(to, size);

    if hypervisor_ptable
        .identity_map(to, to_end, Mode::W, ppool)
        .is_err()
    {
        return false;
    }

    memcpy_s(pa_addr(to) as *mut _, size, from, size);
    arch_mm_write_back_dcache(pa_addr(to), size);

    hypervisor_ptable.unmap(to, to_end, ppool);

    true
}

/// Loads the primary VM.
pub unsafe fn load_primary(
    hypervisor_ptable: &mut PageTable<Stage1>,
    cpio: *const MemIter,
    kernel_arg: uintreg_t,
    ppool: &mut MPool,
) -> Result<MemIter, ()> {
    let mut it = mem::uninitialized();
    let primary_begin = layout_primary_begin();

    if !cpio_find_file(cpio, "vmlinuz\0".as_ptr(), &mut it) {
        dlog!("Unable to find vmlinuz\n");
        return Err(());
    }

    dlog!(
        "Copying primary to {:p}\n",
        pa_addr(primary_begin) as *const u8
    );
    if !copy_to_unmapped(
        hypervisor_ptable,
        primary_begin,
        it.next as usize as *mut _,
        it.limit.offset_from(it.next) as usize,
        ppool,
    ) {
        dlog!("Unable to relocate kernel for primary vm.\n");
        return Err(());
    }

    let mut initrd = MaybeUninit::uninit();
    if !cpio_find_file(cpio, "initrd.img\0".as_ptr(), initrd.get_mut()) {
        dlog!("Unable to find initrd.img\n");
        return Err(());
    }

    let initrd = initrd.assume_init();

    {
        let mut vm = mem::uninitialized();
        if !vm_init(MAX_CPUS as u16, ppool, &mut vm) {
            dlog!("Unable to initialise primary vm\n");
            return Err(());
        }

        if (*vm).id != HF_PRIMARY_VM_ID {
            dlog!("Primary vm was not given correct id\n");
            return Err(());
        }

        // Map the 1TB of memory.
        // TODO: We should do a whitelist rather than blacklist.
        if !mm_vm_identity_map(
            &mut (*vm).inner.get_mut_unchecked().ptable,
            pa_init(0),
            pa_init(1024usize * 1024 * 1024 * 1024),
            Mode::R | Mode::W | Mode::X,
            ptr::null_mut(),
            ppool,
        ) {
            dlog!("Unable to initialise memory for primary vm\n");
            return Err(());
        }

        if !mm_vm_unmap_hypervisor(&mut (*vm).inner.get_mut_unchecked().ptable, ppool) {
            dlog!("Unable to unmap hypervisor from primary vm\n");
            return Err(());
        }

        (*vm_get_vcpu(vm, 0))
            .inner
            .lock()
            .on(ipa_from_pa(primary_begin), kernel_arg);
    }

    Ok(initrd)
}

/// Try to find a memory range of the given size within the given ranges, and
/// remove it from them. Return true on success, or false if no large enough
/// contiguous range is found.
unsafe fn carve_out_mem_range(
    mem_ranges: *mut MemRange,
    mem_ranges_count: usize,
    size_to_find: u64,
    found_begin: *mut paddr_t,
    found_end: *mut paddr_t,
) -> bool {
    // TODO(b/116191358): Consider being cleverer about how we pack VMs
    // together, with a non-greedy algorithm.
    for i in 0..mem_ranges_count {
        if size_to_find
            <= pa_difference((*mem_ranges.add(i)).begin, (*mem_ranges.add(i)).end) as u64
        {
            // This range is big enough, take some of it from the end and reduce
            // its size accordingly.
            *found_end = (*mem_ranges.add(i)).end;
            *found_begin = pa_init(pa_addr((*mem_ranges.add(i)).end) - size_to_find as usize);
            (*mem_ranges.add(i)).end = *found_begin;
            return true;
        }
    }

    false
}

/// Given arrays of memory ranges before and after memory was removed for
/// secondary VMs, add the difference to the reserved ranges of the given
/// update. Return true on success, or false if there would be more than
/// MAX_MEM_RANGES reserved ranges after adding the new ones.
/// `before` and `after` must be arrays of exactly `mem_ranges_count` elements.
unsafe fn update_reserved_ranges(
    update: *mut BootParamsUpdate,
    before: *const MemRange,
    after: *const MemRange,
    mem_ranges_count: usize,
) -> Result<(), ()> {
    let after = slice::from_raw_parts(after, mem_ranges_count);
    let before = slice::from_raw_parts(before, mem_ranges_count);

    for (before, after) in before.iter().zip(after.iter()) {
        if pa_addr(after.begin) > pa_addr(before.begin) {
            if (*update).reserved_ranges_count >= MAX_MEM_RANGES {
                dlog!("Too many reserved ranges after loading secondary VMs.\n");
                return Err(());
            }

            (*update).reserved_ranges[(*update).reserved_ranges_count].begin = after.end;
            (*update).reserved_ranges[(*update).reserved_ranges_count].end = before.end;
            (*update).reserved_ranges_count += 1;
        }
    }

    Ok(())
}

/// Loads all secondary VMs into the memory ranges from the given params.
/// Memory reserved for the VMs is added to the `reserved_ranges` of `update`.
pub unsafe fn load_secondary(
    hypervisor_ptable: &mut PageTable<Stage1>,
    cpio: *const MemIter,
    params: *const BootParams,
    update: *mut BootParamsUpdate,
    ppool: &mut MPool,
) -> Result<(), ()> {
    let mut mem_ranges_available: [MemRange; MAX_MEM_RANGES] = mem::uninitialized();
    // static_assert(
    //  sizeof(mem_ranges_available) == sizeof(params->mem_ranges),
    //  "mem_range arrays must be the same size for memcpy.");

    const_assert!(mem::size_of::<MemRange>() * MAX_MEM_RANGES < 500);
    mem_ranges_available.clone_from_slice(&(*params).mem_ranges);

    let primary = vm_find(HF_PRIMARY_VM_ID);
    let mut it = mem::uninitialized();

    if !cpio_find_file(cpio, "vms.txt\0".as_ptr(), &mut it) {
        dlog!("vms.txt is missing\n");
        return Ok(());
    }

    // Round the last addresses down to the page size.
    for i in 0..(*params).mem_ranges_count {
        mem_ranges_available[i].end =
            pa_init(round_down(pa_addr(mem_ranges_available[i].end), PAGE_SIZE));
    }

    let mut mem = mem::uninitialized();
    let mut cpu = mem::uninitialized();
    let mut name = mem::uninitialized();

    while memiter_parse_uint(&mut it, &mut mem)
        && memiter_parse_uint(&mut it, &mut cpu)
        && memiter_parse_str(&mut it, &mut name)
    {
        dlog!("Loading ");
        let mut p = name.next;
        while p != name.limit {
            dlog!("{}", *p as char);
            p = p.add(1);
        }
        dlog!("\n");

        let mut kernel = mem::uninitialized();

        if !cpio_find_file_memiter(cpio, &name, &mut kernel) {
            dlog!("Unable to load kernel\n");
            continue;
        }

        // Round up to page size.
        mem = (mem + PAGE_SIZE as u64 - 1) & !(PAGE_SIZE as u64 - 1);

        if mem < kernel.limit.offset_from(kernel.next) as u64 {
            dlog!("Kernel is larger than available memory\n");
            continue;
        }

        let mut secondary_mem_begin = mem::uninitialized();
        let mut secondary_mem_end = mem::uninitialized();

        if !carve_out_mem_range(
            mem_ranges_available.as_mut_ptr(),
            (*params).mem_ranges_count,
            mem,
            &mut secondary_mem_begin,
            &mut secondary_mem_end,
        ) {
            dlog!("Not enough memory ({} bytes)\n", mem);
            continue;
        }

        if !copy_to_unmapped(
            hypervisor_ptable,
            secondary_mem_begin,
            kernel.next as usize as *const _,
            kernel.limit.offset_from(kernel.next) as usize,
            ppool,
        ) {
            dlog!("Unable to copy kernel\n");
            continue;
        }

        let mut vm = mem::uninitialized();
        if !vm_init(cpu as spci_vcpu_count_t, ppool, &mut vm) {
            dlog!("Unable to initialise VM\n");
            continue;
        }

        let mut secondary_entry = mem::uninitialized();

        // Grant the VM access to the memory.
        if !mm_vm_identity_map(
            &mut (*vm).inner.get_mut_unchecked().ptable,
            secondary_mem_begin,
            secondary_mem_end,
            Mode::R | Mode::W | Mode::X,
            &mut secondary_entry,
            ppool,
        ) {
            dlog!("Unable to initialise memory\n");
            continue;
        }

        // Deny the primary VM access to this memory.
        if !mm_vm_unmap(
            &mut (*primary).inner.get_mut_unchecked().ptable,
            secondary_mem_begin,
            secondary_mem_end,
            ppool,
        ) {
            dlog!("Unable to unmap secondary VM from primary VM\n");
            return Err(());
        }

        dlog!(
            "Loaded with {} vcpus, entry at 0x{:x}\n",
            cpu,
            pa_addr(secondary_mem_begin)
        );

        let vcpu = vm_get_vcpu(vm, 0);
        vcpu_secondary_reset_and_start(
            vcpu,
            secondary_entry,
            pa_difference(secondary_mem_begin, secondary_mem_end) as uintreg_t,
        );
    }

    // Add newly reserved areas to update params by looking at the difference
    // between the available ranges from the original params and the updated
    // mem_ranges_available. We assume that the number and order of available
    // ranges is the same, i.e. we don't remove any ranges above only make them
    // smaller.
    update_reserved_ranges(
        update,
        (*params).mem_ranges.as_ptr(),
        mem_ranges_available.as_ptr(),
        (*params).mem_ranges_count,
    )
}
