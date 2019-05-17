#![allow(non_camel_case_types)]

use core;

pub type c_void = core::ffi::c_void;
pub type c_int = i32;
pub type size_t = usize;
pub type rsize_t = usize;

pub const RSIZE_MAX: rsize_t = rsize_t::max_value() >> 1;
