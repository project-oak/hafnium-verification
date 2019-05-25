#![allow(non_camel_case_types)]

use core::ffi;

pub type c_void = ffi::c_void;
pub type c_int = i32;
pub type c_char = u8;
pub type size_t = usize;
pub type rsize_t = usize;

pub const RSIZE_MAX: rsize_t = rsize_t::max_value() >> 1;

/// The number of virtual interrupt IDs which are supported.
pub const HF_NUM_INTIDS: usize = 64;
