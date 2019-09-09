/*
 * Copyright 2019 Sanguk Park
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

use core::convert::TryInto;
use core::fmt::{self, Write};
use core::mem::MaybeUninit;
use core::ptr;

use crate::fdt::*;
use crate::memiter::*;
use crate::types::*;

use arrayvec::ArrayVec;

const VM_NAME_BUF_SIZE: usize = 2 + 5 + 1; // "vm" + number + null terminator
const_assert!(MAX_VMS <= 99999);

#[derive(PartialEq, Debug)]
pub enum Error {
    NoHypervisorFdtNode,
    NotCompatible,
    ReservedVmId,
    NoPrimaryVm,
    TooManyVms,
    PropertyNotFound,
    MalformedString,
    StringTooLong,
    MalformedStringList,
    MalformedInteger,
    IntegerOverflow,
}

impl Into<&'static str> for Error {
    fn into(self) -> &'static str {
        use Error::*;
        match self {
            NoHypervisorFdtNode => "Could not find \"hypervisor\" node in manifest",
            NotCompatible => "Hypervisor manifest entry not compatible with Hafnium",
            ReservedVmId => "Manifest defines a VM with a reserved ID",
            NoPrimaryVm => "Manifest does not contain a primary VM entry",
            TooManyVms => {
                "Manifest specifies more VMs than Hafnium has statically allocated space for"
            }
            PropertyNotFound => "Property not found",
            MalformedString => "Malformed string property",
            StringTooLong => "String too long",
            MalformedStringList => "Malformed string list property",
            MalformedInteger => "Malformed integer property",
            IntegerOverflow => "Integer overflow",
        }
    }
}

/// Maximum length of a string parsed from the FDT, including NULL terminator.
const MANIFEST_MAX_STRING_LENGTH: usize = 32;

/// Holds information about one of the VMs described in the manifest.
#[derive(Debug)]
pub struct ManifestVm {
    // Properties defined for both primary and secondary VMs.
    pub debug_name: [u8; MANIFEST_MAX_STRING_LENGTH],

    // Properties specific to secondary VMs.
    pub kernel_filename: [u8; MANIFEST_MAX_STRING_LENGTH],
    pub mem_size: u64,
    pub vcpu_count: spci_vcpu_count_t,
}

/// Hafnium manifest parsed from FDT.
#[derive(Debug)]
pub struct Manifest {
    pub vms: ArrayVec<[ManifestVm; MAX_VMS]>,
}

/// Generates a string with the two letters "vm" followed by an integer.
fn generate_vm_node_name<'a>(
    buf: &'a mut [u8; VM_NAME_BUF_SIZE],
    vm_id: spci_vm_id_t,
) -> &'a mut [u8] {
    struct BufWrite<'a> {
        buf: &'a mut [u8; VM_NAME_BUF_SIZE],
        size: usize,
    }

    impl<'a> Write for BufWrite<'a> {
        fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
            let dest = self
                .buf
                .get_mut(self.size..(self.size + s.len()))
                .ok_or(fmt::Error)?;
            dest.copy_from_slice(s.as_bytes());
            self.size += s.len();

            Ok(())
        }
    }

    let mut buf = BufWrite { buf, size: 0 };
    write!(buf, "vm{}\0", vm_id).unwrap();
    &mut buf.buf[..buf.size]
}

impl<'a> FdtNode<'a> {
    /// TODO(HfO2): This function is marked `inline(never)`, to prevent stack overflow. It is still
    /// mysterious why inlining this function into ManifestVm::new makes stack overflow.
    #[inline(never)]
    fn read_string(&self, property: *const u8, out: &mut [u8]) -> Result<(), Error> {
        let data = self
            .read_property(property)
            .map_err(|_| Error::PropertyNotFound)?;

        // Require that the value contains exactly one NULL character and that it is the last byte.
        if data.iter().position(|&c| c == b'\0') != Some(data.len() - 1) {
            return Err(Error::MalformedString);
        }

        // Check that the string fits into the buffer.
        if data.len() > out.len() {
            return Err(Error::StringTooLong);
        }

        out[..data.len()].copy_from_slice(data);
        Ok(())
    }

    #[inline(never)]
    fn read_u64(&self, property: *const u8) -> Result<u64, Error> {
        let data = self
            .read_property(property)
            .map_err(|_| Error::PropertyNotFound)?;

        fdt_parse_number(data).ok_or(Error::MalformedInteger)
    }

    #[inline(never)]
    fn read_u16(&self, property: *const u8) -> Result<u16, Error> {
        let value = self.read_u64(property)?;

        value.try_into().map_err(|_| Error::IntegerOverflow)
    }
}

/// Represents the value of property whose type is a list of strings. These are encoded as one
/// contiguous byte buffer with NULL-separated entries.
#[derive(Clone)]
struct StringList {
    mem_it: MemIter,
}

impl StringList {
    fn read_from<'a>(node: &FdtNode<'a>, property: *const u8) -> Result<Self, Error> {
        let data = node
            .read_property(property)
            .map_err(|_| Error::PropertyNotFound)?;

        // Require that the value ends with a NULL terminator. Other NULL characters separate the
        // string list entries.
        if *data.last().unwrap() != b'\0' {
            return Err(Error::MalformedStringList);
        }

        Ok(Self {
            mem_it: unsafe { MemIter::from_raw(data.as_ptr(), data.len() - 1) },
        })
    }

    fn has_next(&self) -> bool {
        self.mem_it.len() > 0
    }

    fn get_next(&mut self) -> MemIter {
        assert!(self.has_next());

        let null_term = unsafe { self.mem_it.as_slice() }
            .iter()
            .position(|&c| c == b'\0');
        if let Some(pos) = null_term {
            // Found NULL terminator. Set entry memiter to byte range [base, null) and move list
            // memiter past the terminator.
            let ret = unsafe { MemIter::from_raw(self.mem_it.get_next(), pos) };
            self.mem_it.advance(pos + 1).unwrap();
            ret
        } else {
            // NULL terminator not found, this is the last entry.
            // Set entry memiter to the entire byte range and advance list memiter to the end of
            // the byte range.
            let ret = self.mem_it.clone();
            self.mem_it.advance(self.mem_it.len()).unwrap();
            ret
        }
    }

    fn contains(&self, asciz: &[u8]) -> bool {
        let mut it = self.clone();

        while it.has_next() {
            let entry = it.get_next();
            if unsafe { entry.iseq(asciz.as_ptr()) } {
                return true;
            }
        }

        false
    }
}

impl ManifestVm {
    fn new<'a>(node: &FdtNode<'a>, vm_id: spci_vm_id_t) -> Result<Self, Error> {
        let mut debug_name: [u8; MANIFEST_MAX_STRING_LENGTH] = Default::default();
        node.read_string("debug_name\0".as_ptr(), &mut debug_name)?;

        let mut kernel_filename: [u8; MANIFEST_MAX_STRING_LENGTH] = Default::default();

        let (mem_size, vcpu_count) = if vm_id != HF_PRIMARY_VM_ID {
            node.read_string("kernel_filename\0".as_ptr(), &mut kernel_filename)?;
            (
                node.read_u64("mem_size\0".as_ptr())?,
                node.read_u16("vcpu_count\0".as_ptr())?,
            )
        } else {
            (0, 0)
        };

        Ok(Self {
            debug_name,
            kernel_filename,
            mem_size,
            vcpu_count,
        })
    }
}

impl Manifest {
    /// Parse manifest from FDT.
    pub fn init<'a>(&mut self, fdt: &FdtNode<'a>) -> Result<(), Error> {
        let mut vm_name_buf = Default::default();
        let mut found_primary_vm = false;
        unsafe {
            self.vms.set_len(0);
        }

        // Find hypervisor node.
        let mut hyp_node = fdt.clone();
        hyp_node
            .find_child("hypervisor\0".as_ptr())
            .ok_or(Error::NoHypervisorFdtNode)?;

        // Check "compatible" property.
        let compatible_list = StringList::read_from(&hyp_node, "compatible\0".as_ptr())?;
        if !compatible_list.contains(b"hafnium,hafnium\0") {
            return Err(Error::NotCompatible);
        }

        // Iterate over reserved VM IDs and check no such nodes exist.
        for vm_id in 0..HF_VM_ID_OFFSET {
            let mut vm_node = hyp_node.clone();
            let vm_name = generate_vm_node_name(&mut vm_name_buf, vm_id);

            if vm_node.find_child(vm_name.as_ptr()).is_some() {
                return Err(Error::ReservedVmId);
            }
        }

        // Iterate over VM nodes until we find one that does not exist.
        for i in 0..=MAX_VMS as spci_vm_id_t {
            let vm_id = HF_VM_ID_OFFSET + i;
            let mut vm_node = hyp_node.clone();
            let vm_name = generate_vm_node_name(&mut vm_name_buf, vm_id);

            if vm_node.find_child(vm_name.as_ptr()).is_none() {
                break;
            }

            if i == MAX_VMS as spci_vm_id_t {
                return Err(Error::TooManyVms);
            }

            if vm_id == HF_PRIMARY_VM_ID {
                assert!(found_primary_vm == false); // sanity check
                found_primary_vm = true;
            }

            self.vms.push(ManifestVm::new(&vm_node, vm_id)?);
        }

        if !found_primary_vm {
            Err(Error::NoPrimaryVm)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    extern crate std;
    use std::fmt::Write as fmtWrite;
    use std::io::Write;
    use std::mem;
    use std::mem::MaybeUninit;
    use std::process::*;
    use std::string::String;
    use std::vec::Vec;

    use super::*;
    use crate::utils::*;

    /// Class for programatically building a Device Tree.
    ///
    /// # Usage
    /// ```
    /// let dtb = ManifestDtBuilder::new()
    ///     .Command1()
    ///     .Command2()
    ///     ...
    ///     .CommandN()
    ///     .Build();
    /// ```
    struct ManifestDtBuilder {
        dts: String,
    }

    impl ManifestDtBuilder {
        fn new() -> Self {
            let mut builder = Self { dts: String::new() };
            builder.dts.push_str("/dts-v1/;\n");
            builder.dts.push_str("\n");

            // Start root node.
            builder.start_child("/");
            builder
        }

        fn build(&mut self) -> Vec<u8> {
            self.end_child();
            const program: &'static str = "../build/image/dtc.py";

            let mut child = Command::new(program)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .args(&["compile"])
                .spawn()
                .unwrap();

            child
                .stdin
                .as_mut()
                .unwrap()
                .write_all(self.dts.as_bytes())
                .unwrap();

            child.wait_with_output().unwrap().stdout
        }

        fn start_child(&mut self, name: &str) -> &mut Self {
            self.dts.push_str(name);
            self.dts.push_str(" {\n");
            self
        }

        fn end_child(&mut self) -> &mut Self {
            self.dts.push_str("};\n");
            self
        }

        fn compatible(&mut self, value: &[&str]) -> &mut Self {
            self.string_list_property("compatible", value)
        }

        fn compatible_hafnium(&mut self) -> &mut Self {
            self.compatible(&["hafnium,hafnium"])
        }

        fn debug_name(&mut self, value: &str) -> &mut Self {
            self.string_property("debug_name", value)
        }

        fn kernel_filename(&mut self, value: &str) -> &mut Self {
            self.string_property("kernel_filename", value)
        }

        fn vcpu_count(&mut self, value: u64) -> &mut Self {
            self.integer_property("vcpu_count", value)
        }

        fn mem_size(&mut self, value: u64) -> &mut Self {
            self.integer_property("mem_size", value)
        }

        fn string_property(&mut self, name: &str, value: &str) -> &mut Self {
            write!(self.dts, "{} = \"{}\";\n", name, value).unwrap();
            self
        }

        fn string_list_property(&mut self, name: &str, value: &[&str]) -> &mut Self {
            write!(self.dts, "{} = \"", name);
            self.dts.push_str(&value.join("\", \""));
            self.dts.push_str("\";\n");
            self
        }

        fn integer_property(&mut self, name: &str, value: u64) -> &mut Self {
            write!(self.dts, "{} = <{}>;\n", name, value).unwrap();
            self
        }
    }

    fn get_fdt_root<'a>(dtb: &'a [u8]) -> Option<FdtNode<'a>> {
        let fdt_header = unsafe { &*(dtb.as_ptr() as *const FdtHeader) };

        let mut node = FdtNode::new_root(fdt_header)?;
        node.find_child("\0".as_ptr());
        Some(node)
    }

    #[test]
    fn no_hypervisor_node() {
        let dtb = ManifestDtBuilder::new().build();

        let fdt_root = get_fdt_root(&dtb).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        assert_eq!(m.init(&fdt_root).unwrap_err(), Error::NoHypervisorFdtNode);
    }

    #[test]
    fn no_compatible_property() {
        let dtb = ManifestDtBuilder::new()
            .start_child("hypervisor")
            .end_child()
            .build();

        let fdt_root = get_fdt_root(&dtb).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        assert_eq!(m.init(&fdt_root).unwrap_err(), Error::PropertyNotFound);
    }

    #[test]
    fn not_compatible() {
        let dtb = ManifestDtBuilder::new()
            .start_child("hypervisor")
            .compatible(&["foo,bar"])
            .end_child()
            .build();

        let fdt_root = get_fdt_root(&dtb).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        assert_eq!(m.init(&fdt_root).unwrap_err(), Error::NotCompatible);
    }

    #[test]
    fn compatible_one_of_many() {
        let dtb = ManifestDtBuilder::new()
            .start_child("hypervisor")
            .compatible(&["foo,bar", "hafnium,hafnium"])
            .start_child("vm1")
            .debug_name("primary")
            .end_child()
            .end_child()
            .build();

        let fdt_root = get_fdt_root(&dtb).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        m.init(&fdt_root).unwrap();
    }

    #[test]
    fn no_vm_nodes() {
        let dtb = ManifestDtBuilder::new()
            .start_child("hypervisor")
            .compatible_hafnium()
            .end_child()
            .build();

        let fdt_root = get_fdt_root(&dtb).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        assert_eq!(m.init(&fdt_root).unwrap_err(), Error::NoPrimaryVm);
    }

    #[test]
    fn long_string() {
        fn gen_long_string_dtb(valid: bool) -> Vec<u8> {
            const LAST_VALID: &'static str = "1234567890123456789012345678901";
            const FIRST_INVALID: &'static str = "12345678901234567890123456789012";
            assert_eq!(LAST_VALID.len() + 1, MANIFEST_MAX_STRING_LENGTH);
            assert_eq!(FIRST_INVALID.len() + 1, MANIFEST_MAX_STRING_LENGTH + 1);

            ManifestDtBuilder::new()
                .start_child("hypervisor")
                .compatible_hafnium()
                .start_child("vm1")
                .debug_name(if valid { LAST_VALID } else { FIRST_INVALID })
                .end_child()
                .end_child()
                .build()
        }

        let dtb_last_valid = gen_long_string_dtb(true);
        let dtb_first_invalid = gen_long_string_dtb(false);

        let fdt_root = get_fdt_root(&dtb_last_valid).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        m.init(&fdt_root).unwrap();

        let fdt_root = get_fdt_root(&dtb_first_invalid).unwrap();
        assert_eq!(m.init(&fdt_root).unwrap_err(), Error::StringTooLong);
    }

    #[test]
    fn reserved_vm_id() {
        let dtb = ManifestDtBuilder::new()
            .start_child("hypervisor")
            .compatible_hafnium()
            .start_child("vm1")
            .debug_name("primary_vm")
            .end_child()
            .start_child("vm0")
            .debug_name("reserved_vm")
            .vcpu_count(1)
            .mem_size(0x1000)
            .kernel_filename("kernel")
            .end_child()
            .end_child()
            .build();

        let fdt_root = get_fdt_root(&dtb).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        assert_eq!(m.init(&fdt_root).unwrap_err(), Error::ReservedVmId);
    }

    #[test]
    fn vcpu_count_limit() {
        fn gen_vcpu_count_limit_dtb(vcpu_count: u64) -> Vec<u8> {
            ManifestDtBuilder::new()
                .start_child("hypervisor")
                .compatible_hafnium()
                .start_child("vm1")
                .debug_name("primary_vm")
                .end_child()
                .start_child("vm2")
                .debug_name("secondary_vm")
                .vcpu_count(vcpu_count)
                .mem_size(0x1000)
                .kernel_filename("kernel")
                .end_child()
                .end_child()
                .build()
        }

        let dtb_last_valid = gen_vcpu_count_limit_dtb(u16::max_value() as u64);
        let dtb_first_invalid = gen_vcpu_count_limit_dtb(u16::max_value() as u64 + 1);

        let fdt_root = get_fdt_root(&dtb_last_valid).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        m.init(&fdt_root).unwrap();
        assert_eq!(m.vms.len(), 2);
        assert_eq!(m.vms[1].vcpu_count, u16::max_value());

        let fdt_root = get_fdt_root(&dtb_first_invalid).unwrap();
        assert_eq!(m.init(&fdt_root).unwrap_err(), Error::IntegerOverflow);
    }

    #[test]
    fn valid() {
        let dtb = ManifestDtBuilder::new()
            .start_child("hypervisor")
            .compatible_hafnium()
            .start_child("vm1")
            .debug_name("primary_vm")
            .end_child()
            .start_child("vm3")
            .debug_name("second_secondary_vm")
            .vcpu_count(43)
            .mem_size(0x12345)
            .kernel_filename("second_kernel")
            .end_child()
            .start_child("vm2")
            .debug_name("first_secondary_vm")
            .vcpu_count(42)
            .mem_size(12345)
            .kernel_filename("first_kernel")
            .end_child()
            .end_child()
            .build();

        let fdt_root = get_fdt_root(&dtb).unwrap();
        let mut m: Manifest = unsafe { MaybeUninit::uninit().assume_init() };
        m.init(&fdt_root).unwrap();
        assert_eq!(m.vms.len(), 3);

        let vm = &m.vms[0];
        assert_eq!(as_asciz(&vm.debug_name), b"primary_vm");

        let vm = &m.vms[1];
        assert_eq!(as_asciz(&vm.debug_name), b"first_secondary_vm");
        assert_eq!(vm.vcpu_count, 42);
        assert_eq!(vm.mem_size, 12345);
        assert_eq!(as_asciz(&vm.kernel_filename), b"first_kernel");

        let vm = &m.vms[2];
        assert_eq!(as_asciz(&vm.debug_name), b"second_secondary_vm");
        assert_eq!(vm.vcpu_count, 43);
        assert_eq!(vm.mem_size, 0x12345);
        assert_eq!(as_asciz(&vm.kernel_filename), b"second_kernel");
    }
}
