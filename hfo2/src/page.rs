use core::mem;
use core::ops::*;
use core::slice;

use crate::utils::*;

pub const PAGE_BITS: usize = 12;
pub const PAGE_SIZE: usize = 1 << PAGE_BITS;
pub const PAGE_LEVEL_BITS: usize = 9;

#[repr(C, align(4096))]
pub struct RawPage {
    inner: [u8; PAGE_SIZE],
}

const_assert!(raw_page_align; mem::align_of::<RawPage>() == PAGE_SIZE);
const_assert!(raw_page_size; mem::size_of::<RawPage>() == PAGE_SIZE);

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

impl Deref for RawPage {
    type Target = [u8; PAGE_SIZE];

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for RawPage {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
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

impl Drop for Page {
    fn drop(&mut self) {
        panic!("`Page` should not be dropped.");
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
        let new_begin = round_up(ptr as usize, PAGE_SIZE);
        let new_end = round_down(ptr as usize + size, PAGE_SIZE);

        // No pages if there isn't enough room for an entry.
        if new_begin >= new_end || new_end - new_begin < PAGE_SIZE {
            return None;
        }

        Some(Self {
            ptr: new_begin as *mut RawPage,
            size: (new_end - new_begin) / PAGE_SIZE,
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

impl Drop for Pages {
    fn drop(&mut self) {
        panic!("`Pages` should not be dropped.");
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
