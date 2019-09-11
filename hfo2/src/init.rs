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
use crate::api::*;
use crate::arch::*;
use crate::boot_params::*;
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

/// TODO(HfO2): Refactor api.rs and remove `pub` (#44.)
pub struct Hypervisor {
    pub mpool: MPool,
    pub memory_manager: MemoryManager,
    pub cpu_manager: CpuManager,
    pub vm_manager: VmManager,
}

/// Note(HfO2): this variable was originally of type
/// MaybeUninit<[u8; mem::size_of::<RawPageTable>() * HEAP_PAGES]>,
/// but it was not aligned to PAGE_SIZE.
static mut PTABLE_BUF: MaybeUninit<[RawPage; HEAP_PAGES]> = MaybeUninit::uninit();

static mut INITED: bool = false;
/// TODO(HfO2): This `pub` is required by mm_init, which is only used by unit
/// tests. Resolving #46 may help.
pub static mut HAFNIUM: MaybeUninit<Hypervisor> = MaybeUninit::uninit();

/// Performs one-time initialisation of the hypervisor.
#[no_mangle]
unsafe extern "C" fn one_time_init(c: *mut Cpu) -> *mut Cpu {
    if INITED {
        return c;
    }

    // Make sure the console is initialised before calling dlog.
    plat_console_init();

    dlog!("Initialising hafnium\n");

    arch_one_time_init();
    arch_cpu_module_init();

    let mut ppool = MPool::new();
    ppool.free_pages(Pages::from_raw(
        PTABLE_BUF.get_mut().as_mut_ptr(),
        HEAP_PAGES,
    ));

    let mm = MemoryManager::new(&ppool).expect("mm_init failed");

    // We have to initialize memory manager early, because
    // Stage2::invalidate_tlb refers global state. TODO(HfO2): Refactor the
    // function to recieve the info from caller. Maybe MemoryManager should
    // have a wrapper function for page table.
    HAFNIUM.get_mut().memory_manager = mm;
    let mm = &HAFNIUM.get_ref().memory_manager;

    // Enable locks now that mm is initialised.
    dlog_enable_lock();
    mpool_enable_locks();

    let mut hypervisor_ptable = mm.hypervisor_ptable.lock();

    let params = boot_params_get(&mut hypervisor_ptable, &mut ppool)
        .expect("unable to retrieve boot params");

    let cpum = CpuManager::new(
        &params.cpu_ids[..params.cpu_count],
        boot_cpu.id,
        &callstacks,
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

    // Map initrd in, and initialise cpio parser.
    hypervisor_ptable
        .identity_map(params.initrd_begin, params.initrd_end, Mode::R, &ppool)
        .expect("unable to map initrd in");

    let initrd = pa_addr(params.initrd_begin) as *mut _;
    let cpio = MemIter::from_raw(
        initrd,
        pa_difference(params.initrd_begin, params.initrd_end),
    );

    HAFNIUM.get_mut().vm_manager = VmManager::new();

    // Load all VMs.
    let primary_initrd = load_primary(
        &mut HAFNIUM.get_mut().vm_manager,
        &mut hypervisor_ptable,
        &cpio,
        params.kernel_arg,
        &ppool,
    )
    .expect("unable to load primary VM");

    // load_secondary will add regions assigned to the secondary VMs from
    // mem_ranges to reserved_ranges.
    let mut update: BootParamsUpdate = BootParamsUpdate::new(
        pa_from_va(va_from_ptr(primary_initrd.next as usize as *const _)),
        pa_from_va(va_from_ptr(primary_initrd.limit as usize as *const _)),
    );

    load_secondary(
        &mut HAFNIUM.get_mut().vm_manager,
        &mut hypervisor_ptable,
        &cpio,
        &params,
        &mut update,
        &mut ppool,
    )
    .expect("unable to load secondary VMs");

    // Prepare to run by updating bootparams as seen by primary VM.
    boot_params_update(&mut hypervisor_ptable, &mut update, &mut ppool)
        .expect("plat_update_boot_params failed");

    hypervisor_ptable.defrag(&ppool);

    // Initialise HAFNIUM.
    HAFNIUM.get_mut().mpool = ppool;
    HAFNIUM.get_mut().cpu_manager = cpum;

    // Enable TLB invalidation for VM page table updates.
    mm_vm_enable_invalidation();

    dlog!("Hafnium initialisation completed\n");
    INITED = true;

    hafnium().cpu_manager.boot_cpu()

    // From now on, other pCPUs are on in order to run multiple vCPUs. Thus
    // you may safely make readonly references to the Hafnium singleton, but
    // may not modify the singleton without proper locking.
}

pub fn hafnium() -> &'static Hypervisor {
    unsafe { HAFNIUM.get_ref() }
}

// The entry point of CPUs when they are turned on. It is supposed to initialise
// all state and return the first vCPU to run.
#[no_mangle]
pub unsafe extern "C" fn cpu_main(c: *const Cpu) -> *mut VCpu {
    if !mm_cpu_init() {
        panic!("mm_cpu_init failed");
    }

    let primary = hafnium().vm_manager.get(HF_PRIMARY_VM_ID).unwrap();
    let vcpu = primary.vcpus.get(cpu_index(&*c)).unwrap();
    let vm = vcpu.vm;

    // TODO(HfO2): vcpu needs to be borrowed exclusively, which is safe but
    // discouraged. Move this code into one_time_init().
    let vcpu = vcpu as *const _ as usize as *mut VCpu;
    (*vcpu).set_cpu(c);

    // Reset the registers to give a clean start for the primary's vCPU.
    (*vcpu).inner.get_mut().regs.reset(true, &*vm, (*c).id);

    vcpu
}
