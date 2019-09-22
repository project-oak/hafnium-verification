/*
 * Copyright 2019 Sanguk Park.
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

use core::convert::{TryFrom, TryInto};
use core::mem;
use core::ptr;
use core::slice;
use core::str;

use scopeguard::guard;

/// TODO(HfO2): port this function into `std.rs` (#48.)
extern "C" {
    fn strcmp(a: *const u8, b: *const u8) -> i64;
}

#[derive(Clone)]
#[repr(C)]
pub struct fdt_node {
    hdr: *const FdtHeader,
    begin: *const u8,
    end: *const u8,
    strs: *const u8,
}

#[derive(Clone)]
pub struct FdtNode<'a> {
    hdr: &'a FdtHeader,
    data: &'a [u8],
    strs: &'a [u8],
}

impl<'a> From<fdt_node> for FdtNode<'a> {
    fn from(n: fdt_node) -> Self {
        unsafe {
            let hdr = &*n.hdr;
            let data_size = u32::from_be(hdr.size_dt_struct) as usize;
            let strs_size = u32::from_be(hdr.size_dt_strings) as usize;

            Self {
                hdr,
                data: slice::from_raw_parts(n.begin, data_size),
                strs: slice::from_raw_parts(n.strs, strs_size),
            }
        }
    }
}

impl<'a> From<FdtNode<'a>> for fdt_node {
    fn from(n: FdtNode<'a>) -> Self {
        Self {
            hdr: n.hdr,
            begin: n.data.as_ptr(),
            end: unsafe { n.data.as_ptr().add(n.data.len()) },
            strs: n.strs.as_ptr(),
        }
    }
}

#[repr(C)]
pub struct FdtHeader {
    magic: u32,
    totalsize: u32,
    off_dt_struct: u32,
    off_dt_strings: u32,
    off_mem_rsvmap: u32,
    version: u32,
    last_comp_version: u32,
    boot_cpuid_phys: u32,
    size_dt_strings: u32,
    size_dt_struct: u32,
}

struct FdtReserveEntry {
    address: u64,
    size: u64,
}

#[derive(PartialEq, Clone, Copy)]
enum FdtToken {
    BeginNode = 1,
    EndNode = 2,
    Prop = 3,
    Nop = 4,
    End = 9,
}

impl TryFrom<u32> for FdtToken {
    type Error = ();

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        use FdtToken::*;

        match value {
            1 => Ok(BeginNode),
            2 => Ok(EndNode),
            3 => Ok(Prop),
            4 => Ok(Nop),
            9 => Ok(End),
            _ => Err(()),
        }
    }
}

struct FdtTokenizer<'a> {
    cur: &'a [u8],
    strs: &'a [u8],
}

const FDT_VERSION: u32 = 17;
const FDT_MAGIC: u32 = 0xd00d_feed;
const FDT_TOKEN_ALIGNMENT: usize = mem::size_of::<u32>();

impl<'a> FdtTokenizer<'a> {
    fn new(cur: &'a [u8], strs: &'a [u8]) -> Self {
        Self { cur, strs }
    }

    fn align(&mut self) {
        let modular = self.cur.as_ptr() as usize % FDT_TOKEN_ALIGNMENT;
        let (_, cur) = self
            .cur
            .split_at((FDT_TOKEN_ALIGNMENT - modular) % FDT_TOKEN_ALIGNMENT);
        self.cur = cur;
    }

    fn bytes(&mut self, size: usize) -> Option<&'a [u8]> {
        if self.cur.len() < size {
            return None;
        }

        let (first, rest) = self.cur.split_at(size);
        self.cur = rest;
        self.align();

        Some(first)
    }

    fn bytes_filter<F>(&mut self, size: usize, pred: F) -> Option<&'a [u8]>
    where
        F: FnOnce(&'a [u8]) -> bool,
    {
        if self.cur.len() < size {
            return None;
        }

        let (first, rest) = self.cur.split_at(size);
        if !pred(first) {
            return None;
        }
        self.cur = rest;
        self.align();

        Some(first)
    }

    fn u32(&mut self) -> Option<u32> {
        let bytes = self.bytes(mem::size_of::<u32>())?;
        Some(u32::from_be_bytes(bytes.try_into().unwrap()))
    }

    fn u32_expect(&mut self, expect: u32) -> Option<u32> {
        let bytes = self.bytes_filter(mem::size_of::<u32>(), |b| b == expect.to_be_bytes())?;
        Some(u32::from_be_bytes(bytes.try_into().unwrap()))
    }

    fn token(&mut self) -> Option<FdtToken> {
        while let Some(v) = self.u32() {
            let token = v.try_into().unwrap();
            if token != FdtToken::Nop {
                return Some(token);
            }
        }

        None
    }

    fn token_expect(&mut self, expect: FdtToken) -> Option<FdtToken> {
        while let Some(v) = self.u32_expect(expect as u32) {
            let token = v.try_into().unwrap();
            if token != FdtToken::Nop {
                return Some(token);
            }
        }

        None
    }

    fn str(&mut self) -> Option<&'a [u8]> {
        let (i, _) = self.cur.iter().enumerate().find(|(_, p)| **p == 0)?;

        // Found the end of the string.
        let (first, rest) = self.cur.split_at(i + 1);
        self.cur = rest;
        self.align();
        Some(first)
    }

    /// Move cursor to the end so that caller won't get any new tokens.
    fn collapse(&mut self) {
        self.cur = &self.cur[self.cur.len()..];
    }

    fn next_property(&mut self) -> Option<(*const u8, &'a [u8])> {
        self.token_expect(FdtToken::Prop)?;

        let mut this = guard(self, |this| {
            this.collapse();
        });

        let size = this.u32()? as usize;
        let nameoff = this.u32()? as usize;
        let buf = this.bytes(size)?;

        //TODO: Need to verify the strings.
        let name = this.strs[nameoff..].as_ptr();

        mem::forget(this);
        Some((name, buf))
    }

    fn next_subnode(&mut self) -> Option<&'a [u8]> {
        self.token_expect(FdtToken::BeginNode)?;

        let name = some_or!(self.str(), {
            self.collapse();
            return None;
        });

        Some(name)
    }

    fn skip_properties(&mut self) {
        while self.next_property().is_some() {}
    }

    fn skip_node(&mut self) -> Option<()> {
        let mut pending = 1;
        self.skip_properties();

        while pending != 0 {
            while let Some(_) = self.next_subnode() {
                self.skip_properties();
                pending += 1;
            }

            if self.token()? != FdtToken::EndNode {
                self.collapse();
                return None;
            }

            pending -= 1;
        }

        Some(())
    }
}

impl<'a> FdtNode<'a> {
    pub fn new_root(hdr: &'a FdtHeader) -> Option<Self> {
        // Check the magic number before anything else.
        if hdr.magic != u32::from_be(FDT_MAGIC) {
            return None;
        }

        // Check the version.
        let max_ver = u32::from_be(hdr.version);
        let min_ver = u32::from_be(hdr.last_comp_version);
        if FDT_VERSION < min_ver || FDT_VERSION > max_ver {
            return None;
        }

        let hdr_ptr = hdr as *const _ as *const u8;

        let data_begin = u32::from_be(hdr.off_dt_struct) as usize;
        let data_size = u32::from_be(hdr.size_dt_struct) as usize;

        let strs_begin = u32::from_be(hdr.off_dt_strings) as usize;
        let strs_size = u32::from_be(hdr.size_dt_strings) as usize;

        // TODO: Verify that it is all within the fdt.
        // TODO: Verify strings as well.
        Some(FdtNode {
            hdr,
            data: unsafe { slice::from_raw_parts(hdr_ptr.add(data_begin), data_size) },
            strs: unsafe { slice::from_raw_parts(hdr_ptr.add(strs_begin), strs_size) },
        })
    }

    pub fn read_property(&self, name: *const u8) -> Result<&'a [u8], ()> {
        let mut t = FdtTokenizer::new(self.data, self.strs);
        while let Some((prop_name, buf)) = t.next_property() {
            if unsafe { strcmp(prop_name, name) } == 0 {
                return Ok(buf);
            }
        }

        Err(())
    }

    pub fn first_child(&mut self) -> Option<&'a [u8]> {
        let mut t = FdtTokenizer::new(self.data, self.strs);

        t.skip_properties();

        let child_name = t.next_subnode()?;
        self.data = t.cur;

        Some(child_name)
    }

    pub fn next_sibling(&mut self) -> Option<&'a [u8]> {
        let mut t = FdtTokenizer::new(self.data, self.strs);

        t.skip_node()?;
        let sibling_name = t.next_subnode()?;
        self.data = t.cur;

        Some(sibling_name)
    }

    pub fn find_child(&mut self, child: *const u8) -> Option<()> {
        let mut t = FdtTokenizer::new(self.data, self.strs);
        t.skip_properties();

        while let Some(name) = t.next_subnode() {
            if unsafe { strcmp(name.as_ptr(), child) } == 0 {
                self.data = t.cur;
                return Some(());
            }

            t.skip_node();
        }

        None
    }
}

impl FdtHeader {
    pub fn dump(&self) {
        unsafe fn asciz_to_utf8(ptr: *const u8) -> &'static str {
            let len = (0..).find(|i| *ptr.add(*i) != 0).unwrap();
            let bytes = slice::from_raw_parts(ptr, len);
            str::from_utf8_unchecked(bytes)
        }

        // Traverse the whole thing.
        let node = some_or!(FdtNode::new_root(self), {
            dlog!("FDT failed validation.\n");
            return;
        });

        let mut t = FdtTokenizer::new(node.data, node.strs);
        let mut depth = 0;

        loop {
            while let Some(name) = t.next_subnode() {
                dlog!("{:1$}New node: \"{2}\"\n", "", 2 * depth, unsafe {
                    str::from_utf8_unchecked(name)
                });
                depth += 1;
                while let Some((name, buf)) = t.next_property() {
                    dlog!("{:1$}property: \"{2}\" (", "", 2 * depth, unsafe {
                        asciz_to_utf8(name)
                    });
                    for (i, byte) in buf.iter().enumerate() {
                        dlog!("{}{:02x}", if i == 0 { "" } else { " " }, *byte);
                    }
                    dlog!(")\n");
                }
            }

            if t.token().filter(|t| *t != FdtToken::EndNode).is_none() {
                return;
            }

            depth -= 1;

            if depth == 0 {
                break;
            }
        }

        dlog!(
            "fdt: off_mem_rsvmap={}\n",
            u32::from_be(self.off_mem_rsvmap)
        );

        let mut entry = (self as *const _ as usize + u32::from_be(self.off_mem_rsvmap) as usize)
            as *const FdtReserveEntry;

        unsafe {
            while (*entry).address != 0 || (*entry).size != 0 {
                dlog!(
                    "Entry: {:p} (0x{:x} bytes)\n",
                    u64::from_be((*entry).address) as *const u8,
                    u64::from_be((*entry).size)
                );
                entry = entry.add(1);
            }
        }
    }

    pub unsafe fn add_mem_reservation(&mut self, addr: u64, len: u64) {
        // TODO: Clean this up.
        let begin =
            (self as *const _ as usize as *mut u8).add(u32::from_be(self.off_mem_rsvmap) as usize);
        #[allow(clippy::cast_ptr_alignment)]
        let e = begin as *mut FdtReserveEntry;
        let old_size = (u32::from_be(self.totalsize) - u32::from_be(self.off_mem_rsvmap)) as usize;

        self.totalsize =
            (u32::from_be(self.totalsize) + mem::size_of::<FdtReserveEntry>() as u32).to_be();
        self.off_dt_struct =
            (u32::from_be(self.off_dt_struct) + mem::size_of::<FdtReserveEntry>() as u32).to_be();
        self.off_dt_strings =
            (u32::from_be(self.off_dt_strings) + mem::size_of::<FdtReserveEntry>() as u32).to_be();

        ptr::copy(
            begin,
            begin.add(mem::size_of::<FdtReserveEntry>()),
            old_size,
        );

        (*e).address = addr.to_be();
        (*e).size = len.to_be();
    }

    pub fn total_size(&self) -> u32 {
        u32::from_be(self.totalsize)
    }
}

#[no_mangle]
pub unsafe extern "C" fn fdt_root_node(node: *mut fdt_node, hdr: *const FdtHeader) -> bool {
    let n = some_or!(FdtNode::new_root(&*hdr), return false);
    ptr::write(node, n.into());
    true
}

#[no_mangle]
pub unsafe extern "C" fn fdt_find_child(c_node: *mut fdt_node, child: *const u8) -> bool {
    let mut node = FdtNode::from((*c_node).clone());
    let ret = node.find_child(child).is_some();
    ptr::write(c_node, node.into());
    ret
}

#[no_mangle]
pub unsafe extern "C" fn fdt_read_property(
    node: *const fdt_node,
    name: *const u8,
    buf: *mut *const u8,
    size: *mut u32,
) -> bool {
    let prop_buf = ok_or!(
        FdtNode::from((*node).clone()).read_property(name),
        return false
    );
    ptr::write(buf, prop_buf.as_ptr());
    ptr::write(size, prop_buf.len() as u32);
    true
}

#[cfg(test)]
mod test {
    use super::*;

    static TEST_DTB: [u8; 12 * 27] = [
        0xd0, 0x0d, 0xfe, 0xed, 0x00, 0x00, 0x01, 0x44, 0x00, 0x00, 0x00, 0x38, 0x00, 0x00, 0x01,
        0x08, 0x00, 0x00, 0x00, 0x28, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x3c, 0x00, 0x00, 0x00, 0xd0, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x0a, 0x00, 0x00, 0x00,
        0x00, 0x53, 0x6f, 0x6d, 0x65, 0x4d, 0x6f, 0x64, 0x65, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x03, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x06, 0x4e, 0x6f, 0x74, 0x68, 0x69,
        0x6e, 0x67, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x11,
        0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00,
        0x20, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x01, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79,
        0x40, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x07, 0x00,
        0x00, 0x00, 0x2c, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03,
        0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x38, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00,
        0x00, 0x01, 0x63, 0x70, 0x75, 0x73, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00,
        0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x03,
        0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x02, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x09, 0x6d, 0x6f, 0x64, 0x65, 0x6c, 0x00,
        0x63, 0x6f, 0x6d, 0x70, 0x61, 0x74, 0x69, 0x62, 0x6c, 0x65, 0x00, 0x23, 0x61, 0x64, 0x64,
        0x72, 0x65, 0x73, 0x73, 0x2d, 0x63, 0x65, 0x6c, 0x6c, 0x73, 0x00, 0x23, 0x73, 0x69, 0x7a,
        0x65, 0x2d, 0x63, 0x65, 0x6c, 0x6c, 0x73, 0x00, 0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x5f,
        0x74, 0x79, 0x70, 0x65, 0x00, 0x72, 0x65, 0x67, 0x00,
    ];

    #[test]
    fn total_size() {
        let header = (&TEST_DTB[..]).as_ptr() as usize as *const FdtHeader;
        assert_eq!(
            unsafe { (*header).total_size() } as usize,
            mem::size_of_val(&TEST_DTB)
        );
    }
}
