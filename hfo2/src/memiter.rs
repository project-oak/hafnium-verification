use core::ptr;

use crate::std::*;
use crate::types::*;

#[repr(C)]
#[derive(Clone)]
pub struct MemIter {
    next: *const u8,
    limit: *const u8,
}

/// Determines if a character is a whitespace.
fn is_space(c: u8) -> bool {
    match c as char {
        ' ' | '\t' | '\n' | '\r' => true,
        _ => false,
    }
}

fn as_digit(c: u8) -> Option<u8> {
    if '0' as u8 <= c && c <= '9' as u8 {
        Some(c - '0' as u8)
    } else {
        None
    }
}

impl MemIter {
    /// Initialises the given memory iterator.
    pub unsafe fn from_raw(data: *const u8, size: usize) -> Self {
        Self {
            next: data,
            limit: data.add(size),
        }
    }

    /// Moves iterator to the next non-whitespace character.
    unsafe fn skip_space(&mut self) {
        while let Some(c) = self.peek() {
            if !is_space(c) {
                break;
            }
            self.next = self.next.add(1);
        }
    }

    /// Compares the iterator to a null-terminated string.
    pub unsafe fn iseq(&self, str: *const u8) -> bool {
        let self_len = self.limit as usize - self.next as usize;
        let len = strnlen_s(str, self_len + 1);

        len == self_len && memcmp_rs(self.next as *const _, str as *const _, len) == 0
    }

    /// Peeks the first byte.
    unsafe fn peek(&self) -> Option<u8> {
        if self.next < self.limit {
            Some(*self.next)
        } else {
            None
        }
    }

    /// Retrieves the next string that is delimited by whitespaces.
    pub unsafe fn parse_str(&mut self) -> Option<MemIter> {
        // Skip all white space.
        self.skip_space();

        // Find the end of the string.
        let next = self.next;
        while let Some(c) = self.peek() {
            if is_space(c) {
                break;
            }
            self.next = self.next.add(1);
        }

        let size = self.next as usize - next as usize;

        // Fail if we reach the end of the buffer.
        if size == 0 {
            return None;
        }

        Some(MemIter::from_raw(next, size))
    }

    /// Parses the next string that represents a 64-bit number.
    pub unsafe fn parse_uint(&mut self) -> Option<u64> {
        // Skip all white space.
        self.skip_space();

        // Find the number.
        let next = self.next;
        let mut value = 0;
        while let Some(d) = self.peek().and_then(as_digit) {
            value = value * 10 + d as u64;
            self.next = self.next.add(1);
        }

        // Fail if it's not a number.
        if self.next as usize == next as usize {
            return None;
        }

        Some(value)
    }

    /// Advances the iterator by the given number of bytes. Returns true if the iterator was
    /// advanced without going over its limit; returns false and leaves the iterator unmodified
    /// otherwise.
    pub unsafe fn advance(&mut self, v: usize) -> bool {
        let p = self.next.wrapping_add(v);

        if !(self.next <= p && p <= self.limit) {
            return false;
        }

        self.next = p;
        true
    }

    pub unsafe fn read(&mut self, v: usize) -> Option<*const u8> {
        let next = self.next;
        if self.advance(v) {
            Some(next)
        } else {
            None
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn memiter_init(it: *mut MemIter, data: *const c_void, size: size_t) {
    ptr::write(it, MemIter::from_raw(data as *const _, size));
}

#[no_mangle]
pub unsafe extern "C" fn memiter_parse_uint(it: *mut MemIter, value: *mut u64) -> bool {
    (*it).parse_uint().map(|v| *value = v).is_some()
}

#[no_mangle]
pub unsafe extern "C" fn memiter_parse_str(it: *mut MemIter, str: *mut MemIter) -> bool {
    (*it).parse_str().map(|s| *str = s).is_some()
}

#[no_mangle]
pub unsafe extern "C" fn memiter_iseq(it: *const MemIter, str: *const u8) -> bool {
    (*it).iseq(str)
}

#[no_mangle]
pub unsafe extern "C" fn memiter_advance(it: *mut MemIter, v: size_t) -> bool {
    (*it).advance(v as usize)
}
