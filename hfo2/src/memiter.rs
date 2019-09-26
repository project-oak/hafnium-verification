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

use core::ptr;
use core::slice;

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
    if b'0' <= c && c <= b'9' {
        Some(c - b'0')
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
            value = value * 10 + u64::from(d);
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
    pub fn advance(&mut self, v: usize) -> Result<(), ()> {
        let p = self.next.wrapping_add(v);

        if !(self.next <= p && p <= self.limit) {
            return Err(());
        }

        self.next = p;
        Ok(())
    }

    pub fn read(&mut self, v: usize) -> Option<*const u8> {
        let next = self.next;
        if self.advance(v).is_ok() {
            Some(next)
        } else {
            None
        }
    }

    pub fn get_next(&self) -> *const u8 {
        self.next
    }

    pub fn get_limit(&self) -> *const u8 {
        self.limit
    }

    pub unsafe fn as_slice(&self) -> &[u8] {
        slice::from_raw_parts(self.next, self.limit.offset_from(self.next) as usize)
    }

    pub fn len(&self) -> usize {
        unsafe { self.limit.offset_from(self.next) as usize }
    }
}

#[no_mangle]
pub unsafe extern "C" fn memiter_init(it: *mut MemIter, data: *const c_void, size: size_t) {
    ptr::write(it, MemIter::from_raw(data as *const _, size));
}

#[no_mangle]
pub unsafe extern "C" fn memiter_parse_str(it: *mut MemIter, str: *mut MemIter) -> bool {
    (*it).parse_str().map(|s| *str = s).is_some()
}

#[no_mangle]
pub unsafe extern "C" fn memiter_iseq(it: *const MemIter, str: *const u8) -> bool {
    (*it).iseq(str)
}
