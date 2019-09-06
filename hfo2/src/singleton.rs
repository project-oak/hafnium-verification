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

//! A module collecting all the singleton objects in Hafnium.
//!
//! This module is dependency-free; Typical solutions of mutable and shared
//! static objects delay their initialization. Considering concurrency, they
//! often use std::sync features to prevent racy initialization. But Hafnium is
//! different.
//!
//!  - The initialization is _always_ happened once in the specific time.
//!  - During the time, no other thread is running; Hafnium runs as if it were
//!    a single-thread program.
//!  - After the initialization, Hafnium may make a non-exclusive reference of
//!    singletons, but they have their own way for Hafnium to safely write them.
//!
//! Therefore, I do not use a safe wrapper for initialization such as
//! `std::sync::Once` and `lazy_static`.
//!
//! # Safety
//!
//! Hafnium has two states representing its overall life.
//!  - Initializing.
//!  - Exception handling.
//!
//! Hafnium starts from initializing but eventually moves into exception
//! handling state. Thus I treat exception handling state as if it were
//! Hafnium's _usual_ mode; that's why `{memory, vm, api, cpu}_manager`
//! functions are not denoted by `unsafe`. On the other hand, initializers must
//! not be called in the handling state, so that they are `unsafe`.
//!
//! Setting singleton getters as safe causes one problem, that calling one of
//! those functions in initalizing sequence is dangerous if the singleton were
//! not yet initialized. Watch your code!

use core::mem::MaybeUninit;

use crate::api::ApiManager;
use crate::cpu::CpuManager;
use crate::mm::MemoryManager;
use crate::vm::VmManager;

// Singletons.
static mut MEMORY_MANAGER: MaybeUninit<MemoryManager> = MaybeUninit::uninit();
static mut VM_MANAGER: MaybeUninit<VmManager> = MaybeUninit::uninit();
static mut API_MANAGER: MaybeUninit<ApiManager> = MaybeUninit::uninit();
static mut CPU_MANAGER: MaybeUninit<CpuManager> = MaybeUninit::uninit();

// Singleton initializers.
pub unsafe fn memory_manager_init(mm: MemoryManager) {
    MEMORY_MANAGER = MaybeUninit::new(mm);
}

pub unsafe fn vm_manager_init(vmm: VmManager) {
    VM_MANAGER = MaybeUninit::new(vmm);
}

pub unsafe fn api_manager_init(apim: ApiManager) {
    API_MANAGER = MaybeUninit::new(apim);
}

pub unsafe fn cpu_manager_init(cpum: CpuManager) {
    CPU_MANAGER = MaybeUninit::new(cpum);
}

// Global functions to acquire read-only references to singletons.
pub fn memory_manager() -> &'static MemoryManager {
    unsafe { MEMORY_MANAGER.get_ref() }
}

pub fn vm_manager() -> &'static VmManager {
    unsafe { VM_MANAGER.get_ref() }
}

pub fn api_manager() -> &'static ApiManager {
    unsafe { API_MANAGER.get_ref() }
}

pub fn cpu_manager() -> &'static CpuManager {
    unsafe { CPU_MANAGER.get_ref() }
}
