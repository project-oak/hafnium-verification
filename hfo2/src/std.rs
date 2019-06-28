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

use core::mem;
use core::ptr;

use crate::types::*;

#[no_mangle]
pub unsafe extern "C" fn memset_s(dest: *const c_void, destsz: size_t, ch: c_int, count: size_t) {
    if dest.is_null() || destsz > RSIZE_MAX || count > RSIZE_MAX || count > destsz {
        panic!("memset_s failure");
    }

    ptr::write_bytes(dest as *mut u8, ch as u8, count);
}

#[no_mangle]
pub unsafe extern "C" fn memcpy_s(
    dest: *mut c_void,
    destsz: size_t,
    src: *const c_void,
    count: size_t,
) {
    let d = dest as usize;
    let s = src as usize;

    if dest.is_null() || src.is_null()
        || destsz > RSIZE_MAX || count > RSIZE_MAX
        || count > destsz
    // Destination overlaps the end of source.
        || (d > s && d < s + count)
    // Source overlaps the end of destination.
        || (s > d && s < d + destsz)
    {
        panic!("memcpy_s failure");
    }

    // TODO: consider wrapping?

    ptr::copy(src as *const u8, dest as *mut u8, count);
}

#[no_mangle]
pub unsafe extern "C" fn memmove_s(
    dest: *mut c_void,
    destsz: size_t,
    src: *const c_void,
    count: size_t,
) {
    if dest.is_null() || src.is_null() || destsz > RSIZE_MAX || count > RSIZE_MAX || count > destsz
    {
        panic!("memmove_s failure");
    }

    // FIXME(@jeehoonkang): `ptr::copy_nonoverlapping()` is more appropriate here, but using it
    // makes Hafnium crash at boot.
    ptr::copy(src as *const u8, dest as *mut u8, count);
}

#[no_mangle]
pub unsafe extern "C" fn strnlen_s(str: *const c_char, mut strsz: size_t) -> size_t {
    if str.is_null() {
        return 0;
    }

    let mut p = str;
    while strsz > 0 && *p != 0 {
        strsz -= 1;
        p = p.add(1);
    }

    ((p as usize) - (str as usize)) / mem::size_of::<c_char>()
}

pub(crate) unsafe fn memcmp_rs(a: *const c_void, b: *const c_void, mut n: size_t) -> c_int {
    let mut a = a as *const u8;
    let mut b = b as *const u8;

    while n > 0 {
        let cmp = *a - *b;
        if cmp != 0 {
            return cmp as c_int;
        }

        a = a.add(1);
        b = b.add(1);
        n -= 1;
    }

    0
}
