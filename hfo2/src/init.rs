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

use crate::addr::*;
use crate::api::*;
use crate::boot_params::{self, BootParamsUpdate};
use crate::cpu::*;
use crate::load::*;
use crate::memiter::*;
use crate::mm::*;
use crate::mpool::*;
use crate::page::*;
use crate::singleton::*;
use crate::types::*;
use crate::vm::*;

extern "C" {
    fn plat_console_init();
    fn arch_one_time_init();
    fn dlog_enable_lock();
}

/// Note(HfO2): this variable was originally of type
/// MaybeUninit<[u8; mem::size_of::<RawPageTable>() * HEAP_PAGES]>,
/// but it was not aligned to PAGE_SIZE.
static mut PTABLE_BUF: MaybeUninit<[RawPage; HEAP_PAGES]> = MaybeUninit::uninit();

/// Performs one-time initialisation of the hypervisor.
unsafe fn one_time_init() {
    // Make sure the console is initialised before calling dlog.
    plat_console_init();

    dlog!("Initialising hafnium\n");

    arch_one_time_init();

    let mut ppool = MPool::new();
    mpool_add_chunk(
        &mut ppool,
        PTABLE_BUF.get_mut().as_mut_ptr() as usize as *mut _,
        mem::size_of_val(PTABLE_BUF.get_ref()),
    );

    let memory_manager = MemoryManager::new(&ppool).expect("mm_init failed");
    MEMORY_MANAGER = MaybeUninit::new(memory_manager);

    // Enable locks now that mm is initialised.
    dlog_enable_lock();
    mpool_enable_locks();

    let mut hypervisor_ptable = MEMORY_MANAGER.get_ref().hypervisor_ptable.lock();

    let mut params = boot_params::get(&mut hypervisor_ptable, &mut ppool)
        .unwrap_or_else(|| panic!("unable to retrieve boot params"));

    cpu_module_init(&mut params.cpu_ids[0], params.cpu_count);

    for i in 0..params.mem_ranges_count {
        dlog!(
            "Memory range: 0x{:x} - 0x{:x}\n",
            pa_addr(params.mem_ranges[i].begin),
            pa_addr(params.mem_ranges[i].end) - 1
        );
    }

    dlog!(
        "Ramdisk range: 0x{:x} - 0x{:x}\n",
        pa_addr(params.initrd_begin),
        pa_addr(params.initrd_end) - 1
    );

    // Map initrd in, and initialise cpio parser.
    if hypervisor_ptable
        .identity_map(params.initrd_begin, params.initrd_end, Mode::R, &ppool)
        .is_err()
    {
        panic!("unable to map initrd in");
    }

    let initrd = pa_addr(params.initrd_begin) as *mut _;

    let mut cpio = mem::uninitialized();
    memiter_init(
        &mut cpio,
        initrd,
        pa_difference(params.initrd_begin, params.initrd_end),
    );

    // Load all VMs.
    let primary_initrd = load_primary(&mut hypervisor_ptable, &cpio, params.kernel_arg, &mut ppool)
        .unwrap_or_else(|_| panic!("unable to load primary VM"));

    // load_secondary will add regions assigned to the secondary VMs from
    // mem_ranges to reserved_ranges.
    let mut update: BootParamsUpdate = BootParamsUpdate::new(
        pa_from_va(va_from_ptr(primary_initrd.next as usize as *const _)),
        pa_from_va(va_from_ptr(primary_initrd.limit as usize as *const _)),
    );

    if load_secondary(
        &mut hypervisor_ptable,
        &cpio,
        &params,
        &mut update,
        &mut ppool,
    )
    .is_err()
    {
        panic!("unable to load secondary VMs");
    }

    // Prepare to run by updating bootparams as seen by primary VM.
    if boot_params::update(&mut hypervisor_ptable, &mut update, &mut ppool).is_err() {
        panic!("plat_update_boot_params failed");
    }

    hypervisor_ptable.defrag(&ppool);

    // Initialise the API page pool. ppool will be empty from now on.
    api_init(&ppool);

    // Enable TLB invalidation for VM page table updates.
    mm_vm_enable_invalidation();

    dlog!("Hafnium initialisation completed\n");
}

static mut INITED: bool = false;

// The entry point of CPUs when they are turned on. It is supposed to initialise
// all state and return the first vCPU to run.
#[no_mangle]
pub unsafe extern "C" fn cpu_main(c: *mut Cpu) -> *mut VCpu {
    // Do global one-time initialisation just once. We avoid using atomics by
    // only touching the variable from cpu 0.
    if cpu_index(c) == 0 && !INITED {
        INITED = true;
        one_time_init();
    }

    if !mm_cpu_init() {
        panic!("mm_cpu_init failed");
    }

    let vcpu = vm_get_vcpu(vm_find(HF_PRIMARY_VM_ID), cpu_index(c) as spci_vcpu_index_t);
    let vm = (*vcpu).vm;
    vcpu_set_cpu(vcpu, c);

    // Reset the registers to give a clean start for the primary's vCPU.
    (*vcpu)
        .inner
        .get_mut_unchecked()
        .regs
        .reset(true, &*vm, (*c).id);

    vcpu
}
