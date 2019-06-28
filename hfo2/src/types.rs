/*
 * Copyright 2019 Jeehoon Kang
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

#![allow(non_camel_case_types)]

use core::ffi;

use crate::page::*;

pub type c_void = ffi::c_void;
pub type c_int = i32;
pub type c_char = u8;
pub type size_t = usize;
pub type rsize_t = usize;
pub type uintreg_t = usize;

pub const RSIZE_MAX: rsize_t = rsize_t::max_value() >> 1;

pub const HF_NUM_INTIDS: usize = 64;

// TODO(@jeehoonkang)
pub const MAX_CPUS: usize = 32;
pub const MAX_VMS: usize = 128;

pub const HF_MAILBOX_SIZE: usize = PAGE_SIZE;
