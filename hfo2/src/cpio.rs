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

use crate::memiter::*;
use crate::types::*;

extern "C" {
    fn strcmp(a: *const u8, b: *const u8) -> c_int;
}

#[repr(C, packed(1))]
struct CpioHeader {
    magic: u16,
    dev: u16,
    ino: u16,
    mode: u16,
    uid: u16,
    gid: u16,
    nlink: u16,
    rdev: u16,
    mtime: [u16; 2],
    namesize: u16,
    filesize: [u16; 2],
}

pub struct CpioResult {
    name: *const u8,
    contents: *const u8,
    size: usize,
}

/// Retrieves the next file stored in the cpio archive stored in the cpio, and advances the iterator
/// such that another call to this function would return the following file.
pub fn parse_cpio(it: &mut MemIter) -> Option<CpioResult> {
    let header = unsafe { &*(it.read(mem::size_of::<CpioHeader>())? as *const CpioHeader) };

    // TODO: Check magic.

    let name_len = (header.namesize + 1) & !1;
    let name = it.read(name_len as usize)?;

    let contents_len = ((header.filesize[0] as usize) << 16) | header.filesize[1] as usize;
    let contents = it.read((contents_len + 1) & !1)?;

    // TODO: Check that string is null-terminated.

    /* Stop enumerating files when we hit the end marker. */
    if unsafe { strcmp(name, &("TRAILER!!!\n".as_bytes()[0])) } == 0 {
        return None;
    }

    Some(CpioResult {
        name,
        contents,
        size: contents_len,
    })
}

/// Looks for a file in the given cpio archive. The filename is not null-terminated, so we use a
/// memory iterator to represent it. The file, if found, is returned in the `it` argument.
pub fn find_file_memiter(cpio: &MemIter, filename: &MemIter) -> Option<MemIter> {
    let mut iter = cpio.clone();

    while let Some(result) = parse_cpio(&mut iter) {
        if unsafe { filename.iseq(result.name) } {
            return Some(unsafe { MemIter::from_raw(result.contents, result.size) });
        }
    }

    None
}

/// Looks for a file in the given cpio archive. The file, if found, is returned in the `it`
/// argument.
pub unsafe fn find_file(cpio: &MemIter, filename: *const u8) -> Option<MemIter> {
    let mut iter = cpio.clone();

    while let Some(result) = parse_cpio(&mut iter) {
        if strcmp(filename, result.name) == 0 {
            return Some(MemIter::from_raw(result.contents, result.size));
        }
    }

    None
}
