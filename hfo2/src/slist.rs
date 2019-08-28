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

use core::cell::Cell;
use core::marker::PhantomData;
use core::ptr;

/// An entry in an intrusive linked list.
#[derive(Debug)]
#[repr(C)]
pub struct ListEntry {
    /// The next entry in the linked list.
    next: Cell<*const ListEntry>,
}

/// Implementing this trait asserts that the type `T` can be used as an element in the intrusive
/// linked list defined in this module. `T` has to contain (or otherwise be linked to) an instance
/// of `ListEntry`.
///
/// # Example
///
/// ```ignore
/// struct A {
///     entry: ListEntry,
///     data: usize,
/// }
///
/// impl IsElement<A> for A {
///     fn entry_of(a: &A) -> &ListEntry {
///         let entry_ptr = ((a as usize) + offset_of!(A, entry)) as *const ListEntry;
///         unsafe { &*entry_ptr }
///     }
///
///     unsafe fn element_of(entry: &ListEntry) -> &T {
///         let elem_ptr = ((entry as usize) - offset_of!(A, entry)) as *const T;
///         &*elem_ptr
///     }
/// }
/// ```
///
/// This trait is implemented on a type separate from `T` (although it can be just `T`), because
/// one type might be placeable into multiple lists, in which case it would require multiple
/// implementations of `IsElement`. In such cases, each struct implementing `IsElement<T>`
/// represents a distinct `ListEntry` in `T`.
///
/// For example, we can insert the following struct into two lists using `entry1` for one
/// and `entry2` for the other:
///
/// ```ignore
/// struct B {
///     entry1: ListEntry,
///     entry2: ListEntry,
///     data: usize,
/// }
/// ```
///
pub trait IsElement<T> {
    /// Returns a reference to this element's `ListEntry`.
    fn entry_of(element: &T) -> &ListEntry;

    /// Given a reference to an element's entry, returns that element.
    ///
    /// ```ignore
    /// let elem = ListElement::new();
    /// assert_eq!(elem.entry_of(),
    ///            unsafe { ListElement::element_of(elem.entry_of()) } );
    /// ```
    ///
    /// # Safety
    /// The caller has to guarantee that the `ListEntry` it
    /// is called with was retrieved from an instance of the element type (`T`).
    unsafe fn element_of(entry: &ListEntry) -> &T;
}

/// A lock-free, intrusive linked list of type `T`.
#[derive(Debug)]
#[repr(C)]
pub struct List<T, C: IsElement<T> = T> {
    /// The head of the linked list.
    pub(crate) head: ListEntry,

    /// The phantom data for using `T` and `C`.
    _marker: PhantomData<(T, C)>,
}

impl ListEntry {
    pub const fn new() -> Self {
        Self {
            next: Cell::new(ptr::null()),
        }
    }

    /// Inserts `entry` into the head of the list.
    ///
    /// # Safety
    ///
    /// You should guarantee that:
    ///
    /// - `container` is not null
    /// - `container` is immovable, e.g. inside an `Owned`
    /// - the same `ListEntry` is not inserted more than once
    /// - the inserted object will be removed before the list is dropped
    pub unsafe fn push<T, C: IsElement<T>>(&self, element: &T) {
        let entry = C::entry_of(element);
        entry.next.set(self.next.get());
        self.next.set(entry as *const _);
    }
}

impl Default for ListEntry {
    /// Returns the empty entry.
    fn default() -> Self {
        Self::new()
    }
}

impl<T, C: IsElement<T>> List<T, C> {
    /// Returns a new, empty linked list.
    pub const fn new() -> Self {
        Self {
            head: ListEntry::new(),
            _marker: PhantomData,
        }
    }

    /// Inserts `entry` into the head of the list.
    ///
    /// # Safety
    ///
    /// You should guarantee that:
    ///
    /// - `container` is not null
    /// - `container` is immovable, e.g. inside an `Owned`
    /// - the same `ListEntry` is not inserted more than once
    /// - the inserted object will be removed before the list is dropped
    pub unsafe fn push(&mut self, element: &T) {
        self.head.push::<T, C>(element);
    }

    pub unsafe fn pop(&mut self) -> Option<*mut T> {
        let head = self.head.next.get();
        if head.is_null() {
            return None;
        }

        let next = (*head).next.get();
        self.head.next.set(next);
        Some(C::element_of(&*head) as *const _ as *mut _)
    }

    pub unsafe fn pop_if_some<R, F>(&mut self, cond: F) -> Option<(*mut T, R)>
    where
        F: Fn(&T) -> Option<R>,
    {
        let mut prev = &self.head as *const ListEntry;
        let mut curr = self.head.next.get();

        while !curr.is_null() {
            if let Some(result) = cond(C::element_of(&*curr)) {
                (*prev).next.set((*curr).next.get());
                return Some((C::element_of(&*curr) as *const _ as *mut _, result));
            }

            prev = curr;
            curr = (*curr).next.get();
        }

        None
    }
}
