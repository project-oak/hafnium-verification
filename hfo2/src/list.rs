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

//! Doubly circular intrusive linked list with head node, originally from
//! `list.c`.
//! Functions here are not marked by `#[no_mangle]` because there is an inlined
//! declarations on `vm.h` with the same meaning.
//!
//! TODO: It may not be a good design choice to use this data structure. Search
//! for its usages and consider better one.

// TODO: Refactor type names and remove this.
#[allow(non_camel_case_types)]
#[repr(C)]
pub struct ListEntry {
    next: *mut ListEntry,
    prev: *mut ListEntry,
}

#[macro_export]
macro_rules! container_of {
    ($ptr:expr, $type:path, $field:ident) => {
        ($ptr as *const _ as usize - offset_of!($type, $field)) as *mut _
    };
}

#[inline]
pub unsafe fn list_init(e: *mut ListEntry) {
    (*e).next = e;
    (*e).prev = e;
}

#[inline]
pub unsafe fn list_append(l: *mut ListEntry, e: *mut ListEntry) {
    (*e).next = l;
    (*e).prev = (*l).prev;

    (*(*e).next).prev = e;
    (*(*e).prev).next = e;
}

#[inline]
pub unsafe fn list_prepend(l: *mut ListEntry, e: *mut ListEntry) {
    (*e).next = (*l).next;
    (*e).prev = l;

    (*(*e).next).prev = e;
    (*(*e).prev).next = e;
}

#[inline]
pub unsafe fn list_empty(l: *const ListEntry) -> bool {
    (*l).next as *const _ == l
}

#[inline]
pub unsafe fn list_remove(e: *mut ListEntry) {
    (*(*e).prev).next = (*e).next;
    (*(*e).next).prev = (*e).prev;
    list_init(e);
}

#[inline]
pub unsafe fn list_pop_front(l: &ListEntry) -> *mut ListEntry {
    let result = l.next;
    list_remove(result);
    result
}
