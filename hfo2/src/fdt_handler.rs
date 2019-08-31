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

use core::mem;

use crate::fdt::*;

fn convert_number(data: *const u8, size: u32) -> u64 {
    match size {
        mem::size_of::<u32>() => u32::from_be(*(data as usize as *const u32)) as u64,
        mem::size_of::<u64>() => u64::from_be(*(data as usize as *const u64)),
        _ => 0,
    }
}

impl FdtNode {
    fn read_number(&mut self, name: *const u8) -> Option<u64> {
        let mut data = mem::uninitialized();
        let mut size = mem::uninitialized();

        if !self.read_property(name, &mut data, &mut size) {
            return false;
        }

        match size {
            mem::size_of::<u32>() | mem::size_of::<u64>() => {
                Some(convert_number(data, size))
            }
            _ => None,
        }
    }

    fn write_number(&mut self, name: *const u8, value: u64) -> bool {
        let mut data = mem::uninitialized();
        let mut size = mem::uninitialized();
        
        if !self.read_property(name, &mut data, &mut size) {
            return false;
        }

        match size {
            mem::size_of::<u32>() => {
                *(data as *mut u32) = u32::from_be(value);
            }
            mem::size_of::<u64>() => {
                *(data as *mut u64) = u64::from_be(value);
            }
            _ => return false,
        }

        true
    }
    
    /// Finds the memory region where initrd is stored, and updates the fdt node
    /// cursor to the node called "chosen".
    fn find_initrd(&mut self, begin: &mut paddr_t, end: &mut paddr_t) -> bool {
        if self.find_child("chosen\0").is_none() {
            dlog!("Unable to find 'chosen'\n");
            return false;
        }

        let initrd_begin = match self.read_number("linux,initrd-start\0") {
            Some(initrd_begin) => initrd_begin,
            None => {
                dlog!("Unable to read linux,initrd-start\n");
                return false;
            }
        };

        let initrd_end = match self.read_number("linux,initrd-end\0") {
            Some(initrd_end) => initrd_end,
            None => {
                dlog!("Unable to read linux,initrd-end\n");
                return false;
            }
        };

        *begin = pa_init(initrd_begin);
        *end = pa_init(initrd_end);

        true
    }

    fn find_cpus(&self, cpu_ids: &mut cpu_id_t, cpu_count: &mut usize) {
        let node = self.clone();
        *cpu_count = 0;

        if node.find_child("cpus\0").is_none() {
            dlog!("Unable to find 'cpus'\n");
            return;
        }

        
    }
}
