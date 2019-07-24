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

use crate::arch::*;
use crate::types::*;

// TODO: Refactor type names and remove this.
#[allow(non_camel_case_types)]

/// An opaque type for a physical address.
#[repr(C)]
pub struct paddr_t {
    pa: uintpaddr_t,
}

/// An opaque type for an intermediate physical address.
#[repr(C)]
pub struct ipaddr_t {
    ipa: uintpaddr_t,
}

/// An opaque type for a virtual address.
#[repr(C)]
pub struct vaddr_t {
    va: uintvaddr_t,
}

/// Initializes a physical address.
#[inline]
pub fn pa_init(p: uintpaddr_t) -> paddr_t {
    paddr_t { pa: p }
}

/// Extracts the absolute physical address.
#[inline]
pub fn pa_addr(pa: paddr_t) -> uintpaddr_t {
    pa.pa
}

/// Advances a physical address.
#[inline]
pub fn pa_add(pa: paddr_t, n: size_t) -> paddr_t {
    pa_init(pa_addr(pa) + n)
}

/// Returns the difference between two physical addresses.
#[inline]
pub fn pa_difference(start: paddr_t, end: paddr_t) -> size_t {
    pa_addr(end) - pa_addr(start)
}

/// Initializes an intermediate physical address.
#[inline]
pub fn ipa_init(ipa: uintpaddr_t) -> ipaddr_t {
    ipaddr_t { ipa: ipa }
}

/// Extracts the absolute intermediate physical address.
#[inline]
pub fn ipa_addr(ipa: ipaddr_t) -> uintpaddr_t {
    ipa.ipa
}

/// Advances an intermediate physical address.
#[inline]
pub fn ipa_add(ipa: ipaddr_t, n: size_t) -> ipaddr_t {
    ipa_init(ipa_addr(ipa) + n)
}

/// Initializes a virtual address.
#[inline]
pub fn va_init(v: uintvaddr_t) -> vaddr_t {
    vaddr_t { va: v }
}

/// Extracts the absolute virtual address.
#[inline]
pub fn va_addr(va: vaddr_t) -> uintvaddr_t {
    va.va
}

/// Casts a physical address to a virtual address.
#[inline]
pub fn va_from_pa(pa: paddr_t) -> vaddr_t {
    va_init(pa_addr(pa))
}

/// Casts a physical address to an intermediate physical address.
#[inline]
pub fn ipa_from_pa(pa: paddr_t) -> ipaddr_t {
    ipa_init(pa_addr(pa))
}

/// Casts a virtual address to a physical address.
#[inline]
pub fn pa_from_va(va: vaddr_t) -> paddr_t {
    pa_init(va_addr(va))
}

/// Casts an intermediate physical address to a physical address.
#[inline]
pub fn pa_from_ipa(ipa: ipaddr_t) -> paddr_t {
    pa_init(ipa_addr(ipa))
}

/// Casts a pointer to a virtual address.
#[inline]
pub fn va_from_ptr(p: *const c_void) -> vaddr_t {
    vaddr_t {
        va: p as uintvaddr_t,
    }
}

/// Casts a virtual address to a pointer. Only use when the virtual address is
/// mapped for the calling context.
/// TODO: check the mapping for a range and return a memiter?
#[inline]
pub fn ptr_from_va(va: vaddr_t) -> *mut c_void {
    va_addr(va) as *mut c_void
}
