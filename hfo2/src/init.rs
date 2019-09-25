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
use core::ptr;

use crate::addr::*;
use crate::arch::*;
use crate::boot_params::*;
use crate::cpu::*;
use crate::hypervisor::*;
use crate::load::*;
use crate::memiter::*;
use crate::mm::*;
use crate::mpool::*;
use crate::page::*;
use crate::types::*;
use crate::vm::*;

extern "C" {
    fn plat_console_init();
    fn arch_one_time_init();
    fn dlog_enable_lock();

    /// The stack to be used by the CPUs.
    static callstacks: [[u8; STACK_SIZE]; MAX_CPUS];

    /// A record for boot CPU. Its field `stack_bottom` is initialized.
    /// Hafnium loader writes booted CPU ID on `cpus.id` and initializes the CPU
    /// stack by the address in `cpus.stack_bottom`.
    /// (See src/arch/aarch64/hypervisor/plat_entry.S and cpu_entry.S.)
    ///
    /// Initializing static variables with pointers in Rust failed here. We left
    /// the initialization code of `cpus` in `src/cpu.c`.
    static boot_cpu: Cpu;
}

/// Note(HfO2): this variable was originally of type
/// MaybeUninit<[u8; mem::size_of::<RawPageTable>() * HEAP_PAGES]>,
/// but it was not aligned to PAGE_SIZE.
static mut PTABLE_BUF: MaybeUninit<[RawPage; HEAP_PAGES]> = MaybeUninit::uninit();

/// A variable that stores if Hafnium is initialized. This is only read by boot
/// CPU, so its type is not `AtomicBool`.
static mut INITED: bool = false;

/// A singleton collecting all managers in Hafnium.
///
/// This is dependency-free; Typical solutions of mutable and shared static
/// objects delay their initialization. Considering concurrency, they often use
/// std::sync features to prevent racy initialization. But Hafnium is different.
///
///  - The initialization is _always_ happened once in the specific time.
///  - During the time, no other thread is running; Hafnium runs as if it were
///    a single-thread program.
///  - After the initialization, Hafnium may make a non-exclusive reference of
///    singletons, but they have their own way for Hafnium to safely write them.
///
/// Therefore, I do not use a safe wrapper for initialization such as
/// `std::sync::Once` and `lazy_static`.
static mut HYPERVISOR: MaybeUninit<Hypervisor> = MaybeUninit::uninit();

/// Performs one-time initialisation of the hypervisor.
#[no_mangle]
unsafe extern "C" fn one_time_init(c: *const Cpu) -> *const Cpu {
    if &boot_cpu as *const _ != c || INITED {
        return c;
    }

    // Make sure the console is initialised before calling dlog.
    plat_console_init();

    dlog!("Initialising hafnium\n");

    arch_one_time_init();
    arch_cpu_module_init();

    let ppool = MPool::new();
    ppool.free_pages(Pages::from_raw(
        PTABLE_BUF.get_mut().as_mut_ptr(),
        HEAP_PAGES,
    ));

    let mm = MemoryManager::new(&ppool).expect("mm_init failed");

    // Enable locks now that mm is initialised.
    dlog_enable_lock();
    mpool_enable_locks();

    // TODO(HfO2): doesn't need to lock, actually
    let params = boot_params_get(&mut mm.hypervisor_ptable.lock(), &ppool)
        .expect("unable to retrieve boot params");

    let cpum = CpuManager::new(
        &params.cpu_ids[..params.cpu_count],
        boot_cpu.id,
        &callstacks,
    );

    // Initialise HAFNIUM.
    ptr::write(
        HYPERVISOR.get_mut(),
        Hypervisor::new(ppool, mm, cpum, VmManager::new()),
    );

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

    // TODO(HfO2): doesn't need to lock, actually
    let mut hypervisor_ptable = hypervisor().memory_manager.hypervisor_ptable.lock();

    // Map initrd in, and initialise cpio parser.
    hypervisor_ptable
        .identity_map(
            params.initrd_begin,
            params.initrd_end,
            Mode::R,
            &hypervisor().mpool,
        )
        .expect("unable to map initrd in");

    let initrd = pa_addr(params.initrd_begin) as *mut _;
    let cpio = MemIter::from_raw(
        initrd,
        pa_difference(params.initrd_begin, params.initrd_end),
    );

    // Load all VMs.
    let primary_initrd = load_primary(
        &mut HYPERVISOR.get_mut().vm_manager,
        &mut hypervisor_ptable,
        &cpio,
        params.kernel_arg,
        &hypervisor().mpool,
    )
    .expect("unable to load primary VM");

    // load_secondary will add regions assigned to the secondary VMs from
    // mem_ranges to reserved_ranges.
    let mut update: BootParamsUpdate = BootParamsUpdate::new(
        pa_from_va(va_from_ptr(primary_initrd.get_next() as usize as *const _)),
        pa_from_va(va_from_ptr(primary_initrd.get_limit() as usize as *const _)),
    );

    load_secondary(
        &mut HYPERVISOR.get_mut().vm_manager,
        &mut hypervisor_ptable,
        &cpio,
        &params,
        &mut update,
        &hypervisor().mpool,
    )
    .expect("unable to load secondary VMs");

    // Prepare to run by updating bootparams as seen by primary VM.
    boot_params_update(&mut hypervisor_ptable, &mut update, &hypervisor().mpool)
        .expect("plat_update_boot_params failed");

    hypervisor_ptable.defrag(&hypervisor().mpool);

    // Enable TLB invalidation for VM page table updates.
    mm_vm_enable_invalidation();

    dlog!("Hafnium initialisation completed\n");
    INITED = true;

    hypervisor().cpu_manager.get_boot_cpu()

    // From now on, other pCPUs are on in order to run multiple vCPUs. Thus
    // you may safely make readonly references to the Hafnium singleton, but
    // may not modify the singleton without proper locking.
}

pub fn hypervisor() -> &'static Hypervisor {
    unsafe { HYPERVISOR.get_ref() }
}

// The entry point of CPUs when they are turned on. It is supposed to initialise
// all state and return the first vCPU to run.
#[no_mangle]
pub unsafe extern "C" fn cpu_main(c: *const Cpu) -> *const VCpu {
    let raw_ptable = hypervisor().memory_manager.get_raw_ptable();
    MemoryManager::cpu_init(raw_ptable).expect("mm_cpu_init failed");

    let primary = hypervisor().vm_manager.get_primary();
    let vcpu = &primary.vcpus[hypervisor().cpu_manager.index_of(c)];
    let vm = vcpu.vm;

    // TODO(HfO2): vcpu needs to be borrowed exclusively, which is safe but
    // discouraged. Move this code into one_time_init().
    let vcpu_inner = vcpu.inner.get_mut_unchecked();
    vcpu_inner.cpu = c;
    // Reset the registers to give a clean start for the primary's vCPU.
    vcpu_inner.regs.reset(true, &*vm, (*c).id);

    vcpu
}
