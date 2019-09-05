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

use core::mem::MaybeUninit;

use crate::mm::MemoryManager;
use crate::vm::VmManager;

pub static mut MEMORY_MANAGER: MaybeUninit<MemoryManager> = MaybeUninit::uninit();
pub static mut VM_MANAGER: MaybeUninit<VmManager> = MaybeUninit::uninit();
