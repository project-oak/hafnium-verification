#![allow(non_camel_case_types)]

use core::ffi;
use core::mem;
use core::ops::*;
use core::slice;

use crate::utils::*;

pub type c_void = ffi::c_void;
pub type c_int = i32;
pub type c_char = u8;
pub type size_t = usize;
pub type rsize_t = usize;

pub const RSIZE_MAX: rsize_t = rsize_t::max_value() >> 1;

pub const PAGE_BITS: usize = 12;

pub const PAGE_SIZE: usize = 1 << PAGE_BITS;

#[repr(C, align(4096))]
pub struct RawPage {
    inner: [u8; PAGE_SIZE],
}

const_assert!(page_size_4096; PAGE_SIZE == 4096);
const_assert!(page_size_raw_page_size; PAGE_SIZE == mem::size_of::<RawPage>());

impl RawPage {
    pub const fn new() -> Self {
        Self {
            inner: [0; PAGE_SIZE],
        }
    }

    pub fn clear(&mut self) {
        for byte in self.inner.iter_mut() {
            *byte = 0;
        }
    }
}

pub struct Page {
    ptr: *mut RawPage,
}

impl Page {
    pub unsafe fn from_raw(ptr: *mut RawPage) -> Self {
        Self { ptr }
    }

    pub fn into_raw(self) -> *mut RawPage {
        let ptr = self.ptr;
        mem::forget(self);
        ptr
    }
}

impl Deref for Page {
    type Target = RawPage;

    fn deref(&self) -> &Self::Target {
        unsafe { &*(self.ptr as *const Self::Target) }
    }
}

impl DerefMut for Page {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(self.ptr as *mut Self::Target) }
    }
}

pub struct Pages {
    ptr: *mut RawPage,
    size: usize,
}

impl Pages {
    pub unsafe fn from_raw(ptr: *mut RawPage, size: usize) -> Self {
        Self { ptr, size }
    }

    pub unsafe fn from_raw_u8(ptr: *mut u8, size: usize) -> Option<Self> {
        // Round begin address up, and end address down.
        let begin = round_up(ptr as usize, PAGE_SIZE);
        let end = round_down(ptr as usize + size, PAGE_SIZE);

        // No pages if there isn't enough room for an entry.
        if begin >= end || end - begin < PAGE_SIZE {
            return None;
        }

        Some(Self {
            ptr: begin as *mut RawPage,
            size: (end - begin) / PAGE_SIZE,
        })
    }

    pub fn into_raw(self) -> *mut RawPage {
        let ptr = self.ptr;
        mem::forget(self);
        ptr
    }

    pub fn clear(&mut self) {
        for page in self.iter_mut() {
            page.clear();
        }
    }
}

impl Deref for Pages {
    type Target = [RawPage];

    fn deref(&self) -> &Self::Target {
        unsafe { slice::from_raw_parts(self.ptr as *const RawPage, self.size) }
    }
}

impl DerefMut for Pages {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { slice::from_raw_parts_mut(self.ptr as *mut RawPage, self.size) }
    }
}
