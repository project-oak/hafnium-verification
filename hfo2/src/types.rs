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
