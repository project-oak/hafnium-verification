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

use crate::utils::*;

use scopeguard::guard;

/// TODO(HfO2): port this function into `std.rs` (#48.)
extern "C" {
    fn strcmp(a: *const u8, b: *const u8) -> i64;
}

#[derive(Clone)]
#[repr(C)]
pub struct FdtNode {
    hdr: *const FdtHeader,
    begin: *const u8,
    end: *const u8,
    strs: *const u8,
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

#[derive(PartialEq)]
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

struct FdtTokenizer {
    cur: *const u8,
    end: *const u8,
    strs: *const u8,
}

const FDT_VERSION: u32 = 17;
const FDT_MAGIC: u32 = 0xd00d_feed;
const FDT_TOKEN_ALIGNMENT: usize = mem::size_of::<u32>();

impl FdtTokenizer {
    fn new(strs: *const u8, begin: *const u8, end: *const u8) -> Self {
        Self {
            cur: begin,
            end,
            strs,
        }
    }

    fn align(&mut self) {
        self.cur = round_up(self.cur as usize, FDT_TOKEN_ALIGNMENT) as _;
    }

    unsafe fn iter(&self) -> impl Iterator<Item = *const u8> {
        slice::from_raw_parts(self.cur, self.end.offset_from(self.cur) as usize).iter().map(|p| p as *const u8)
    }

    unsafe fn u32(&mut self) -> Option<u32> {
        let next = self.cur.add(mem::size_of::<u32>());
        if next > self.end {
            return None;
        }

        let res = u32::from_be(*(self.cur as usize as *const u32));
        self.cur = next;
        Some(res)
    }

    unsafe fn token(&mut self) -> Option<FdtToken> {
        while let Some(v) = self.u32() {
            let token = v.try_into().unwrap();
            if token != FdtToken::Nop {
                return Some(token);
            }
        }

        None
    }

    unsafe fn bytes(&mut self, size: usize) -> Option<*const u8> {
        let next = self.cur.add(size);

        if next > self.end {
            return None;
        }

        let res = self.cur;
        self.cur = next;
        self.align();

        Some(res)
    }

    unsafe fn str(&mut self) -> Option<*const u8> {
        for p in self.iter() {
            if *p == 0 {
                // Found the end of the string.
                let res = self.cur;
                self.cur = p.add(1);
                self.align();
                return Some(res);
            }
        }

        None
    }

    unsafe fn next_property(&mut self) -> Option<(*const u8, *const u8, u32)> {
        let token = self.token()?;

        if token != FdtToken::Prop {
            // Rewind so that caller will get the same token.
            self.cur = self.cur.sub(mem::size_of::<u32>());
            return None;
        }

        let mut this = guard(self, |this| {
            // Move cursor to the end so that caller won't get any new tokens.
            this.cur = this.end;
        });

        let size = this.u32()?;
        let nameoff = this.u32()?;
        let buf = this.bytes(size as usize)?;

        //TODO: Need to verify the strings.
        let name = this.strs.add(nameoff as usize);

        mem::forget(this);
        Some((name, buf, size))
    }

    unsafe fn next_subnode(&mut self) -> Option<*const u8> {
        let token = self.token()?;
        if token != FdtToken::BeginNode {
            // Rewind so that caller will get the same token.
            self.cur = self.cur.sub(mem::size_of::<u32>());
            return None;
        }

        let name = some_or!(self.str(), {
            // Move cursor to the end so that caller won't get any new
            // tokens.
            self.cur = self.end;
            return None;
        });

        Some(name)
    }

    unsafe fn skip_properties(&mut self) {
        while self.next_property().is_some() {}
    }

    unsafe fn skip_node(&mut self) -> Option<()> {
        let mut pending = 1;
        self.skip_properties();

        while pending != 0 {
            while let Some(_) = self.next_subnode() {
                self.skip_properties();
                pending += 1;
            }

            let token = self.token()?;
            if token != FdtToken::EndNode {
                self.cur = self.end;
                return None;
            }

            pending -= 1;
        }

        Some(())
    }
}

impl FdtNode {
    pub unsafe fn new_root(hdr: &FdtHeader) -> Option<Self> {
        let begin = u32::from_be(hdr.off_dt_struct);
        let size = u32::from_be(hdr.size_dt_struct);

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

        let hdr_ptr = hdr as *const _ as usize as *const u8;

        // TODO: Verify that it is all within the fdt.
        // TODO: Verify strings as well.
        Some(Self {
            hdr: ptr::null(),
            begin: hdr_ptr.add(begin as usize),
            end: hdr_ptr.add((begin + size) as usize),
            strs: hdr_ptr.add(u32::from_be(hdr.off_dt_strings) as usize),
        })
    }

    pub unsafe fn read_property(&self, name: *const u8) -> Result<(*const u8, u32), ()> {
        let mut t = FdtTokenizer::new(self.strs, self.begin, self.end);
        while let Some((prop_name, buf, size)) = t.next_property() {
            if strcmp(prop_name, name) == 0 {
                return Ok((buf, size));
            }
        }

        Err(())
    }

    pub unsafe fn first_child(&mut self) -> Option<*const u8> {
        let mut t = FdtTokenizer::new(self.strs, self.begin, self.end);

        t.skip_properties();

        let child_name = t.next_subnode()?;
        self.begin = t.cur;

        Some(child_name)
    }

    pub unsafe fn next_sibling(&mut self) -> Option<*const u8> {
        let mut t = FdtTokenizer::new(self.strs, self.begin, self.end);

        t.skip_node()?;
        let sibling_name = t.next_subnode()?;
        self.begin = t.cur;

        Some(sibling_name)
    }

    pub unsafe fn find_child(&mut self, child: *const u8) -> Option<()> {
        let mut t = FdtTokenizer::new(self.strs, self.begin, self.end);
        t.skip_properties();

        while let Some(name) = t.next_subnode() {
            if strcmp(name, child) == 0 {
                self.begin = t.cur;
                return Some(());
            }

            t.skip_node();
        }

        None
    }
}

impl FdtHeader {
    pub unsafe fn dump(&self) {
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

        let mut t = FdtTokenizer::new(node.strs, node.begin, node.end);
        let mut depth = 0;

        loop {
            while let Some(name) = t.next_subnode() {
                dlog!(
                    "{:1$}New node: \"{2}\"\n",
                    "",
                    2 * depth,
                    asciz_to_utf8(name)
                );
                depth += 1;
                while let Some((name, buf, size)) = t.next_property() {
                    dlog!(
                        "{:1$}property: \"{2}\" (",
                        "",
                        2 * depth,
                        asciz_to_utf8(name)
                    );
                    for i in 0..size as usize {
                        dlog!("{}{:02x}", if i == 0 { "" } else { " " }, *buf.add(i));
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

        while (*entry).address != 0 || (*entry).size != 0 {
            dlog!(
                "Entry: {:p} (0x{:x} bytes)\n",
                u64::from_be((*entry).address) as *const u8,
                u64::from_be((*entry).size)
            );
            entry = entry.add(1);
        }
    }

    pub unsafe fn add_mem_reservation(&mut self, addr: u64, len: u64) {
        // TODO: Clean this up.
        let begin =
            (self as *const _ as usize as *mut u8).add(u32::from_be(self.off_mem_rsvmap) as usize);
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
pub extern "C" fn fdt_header_size() -> usize {
    mem::size_of::<FdtHeader>()
}

#[no_mangle]
pub unsafe extern "C" fn fdt_total_size(hdr: *const FdtHeader) -> u32 {
    (*hdr).total_size()
}

#[no_mangle]
pub unsafe extern "C" fn fdt_dump(hdr: *mut FdtHeader) {
    (*hdr).dump()
}

#[no_mangle]
pub unsafe extern "C" fn fdt_root_node(node: *mut FdtNode, hdr: *const FdtHeader) -> bool {
    let n = some_or!(FdtNode::new_root(&*hdr), return false);
    ptr::write(node, n);
    true
}

#[no_mangle]
pub unsafe extern "C" fn fdt_find_child(node: *mut FdtNode, child: *const u8) -> bool {
    (*node).find_child(child).is_some()
}

#[no_mangle]
pub unsafe extern "C" fn fdt_first_child(node: *mut FdtNode, child_name: *mut *const u8) -> bool {
    let name = some_or!((*node).first_child(), return false);
    ptr::write(child_name, name);
    true
}

#[no_mangle]
pub unsafe extern "C" fn fdt_next_sibling(
    node: *mut FdtNode,
    sibling_name: *mut *const u8,
) -> bool {
    let name = some_or!((*node).next_sibling(), return false);
    ptr::write(sibling_name, name);
    true
}

#[no_mangle]
pub unsafe extern "C" fn fdt_read_property(
    node: *mut FdtNode,
    name: *const u8,
    buf: *mut *const u8,
    size: *mut u32,
) -> bool {
    let (prop_buf, prop_size) = ok_or!((*node).read_property(name), return false);
    *buf = prop_buf;
    *size = prop_size;
    true
}

#[no_mangle]
pub unsafe extern "C" fn fdt_add_mem_reserveation(hdr: *mut FdtHeader, addr: u64, len: u64) {
    (*hdr).add_mem_reservation(addr, len)
}
