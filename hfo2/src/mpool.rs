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
use core::ops::DerefMut;
use core::ptr;

use crate::list::{IsElement, List, ListEntry};
use crate::page::*;
use crate::spinlock::SpinLock;
use crate::types::*;
use crate::utils::*;

#[repr(C)]
struct Chunk {
    entry: ListEntry,
    size: usize,
}

#[repr(C)]
struct Entry {
    entry: ListEntry,
}

impl Chunk {
    const_assert!(chunk_size; mem::size_of::<Chunk>() <= mem::size_of::<RawPage>());

    pub const fn new(size: usize) -> Self {
        Self {
            entry: ListEntry::new(),
            size,
        }
    }
}

impl Entry {
    const_assert!(entry_size; mem::size_of::<Entry>() <= mem::size_of::<RawPage>());

    pub const fn new() -> Self {
        Self {
            entry: ListEntry::new(),
        }
    }
}

impl IsElement<Chunk> for Chunk {
    fn entry_of(element: &Chunk) -> &ListEntry {
        &element.entry
    }

    unsafe fn element_of(entry: &ListEntry) -> &Chunk {
        &*(entry as *const _ as *const _)
    }
}

impl IsElement<Entry> for Entry {
    fn entry_of(element: &Entry) -> &ListEntry {
        &element.entry
    }

    unsafe fn element_of(entry: &ListEntry) -> &Entry {
        &*(entry as *const _ as *const _)
    }
}

/// Page pool.
#[repr(C)]
pub struct Pool {
    chunk_list: List<Chunk>,
    entry_list: List<Entry>,
}

impl Pool {
    /// Creates a new page pool.
    pub const fn new() -> Self {
        Self {
            chunk_list: List::new(),
            entry_list: List::new(),
        }
    }

    /// Allocates a page.
    pub fn alloc(&mut self) -> Option<Page> {
        if let Some(entry) = unsafe { self.entry_list.pop() } {
            return Some(unsafe { Page::from_raw(entry as *mut RawPage) });
        }

        let chunk = unsafe { self.chunk_list.pop()? };
        let size = unsafe { (*chunk).size };
        assert_ne!(size, 0);
        let page = unsafe { Page::from_raw(chunk as *mut RawPage) };

        if size == 2 {
            let entry = unsafe { &mut *((chunk as usize + PAGE_SIZE) as *mut Entry) };
            unsafe {
                self.entry_list.push(entry);
            }
        } else if size > 2 {
            let new_chunk = unsafe { &mut *((chunk as usize + PAGE_SIZE) as *mut Chunk) };
            new_chunk.size = size - 1;
            unsafe { self.chunk_list.push(new_chunk) };
        }

        Some(page)
    }

    /// Allocates a number of contiguous and aligned pages.
    pub fn alloc_pages(&mut self, size: usize, align: usize) -> Option<Pages> {
        if size == 1 && align == 1 {
            return self
                .alloc()
                .map(|page| unsafe { Pages::from_raw(page.into_raw(), 1) });
        }

        let (chunk, (chunk_start, chunk_end, start, end)) = unsafe {
            self.chunk_list.pop_if_some(|chunk| {
                // Calculate where the new chunk would be if we consume the requested number of
                // entries. Then check if this chunk is big enough to satisfy the request.
                let chunk_size = (*chunk).size;
                let chunk_start = chunk as *const _ as usize;
                let chunk_end = chunk_start + chunk_size * PAGE_SIZE;
                let start = round_up(chunk_start, align * PAGE_SIZE);
                let end = start + size * PAGE_SIZE;

                if chunk_start <= start && start <= end && end <= chunk_end {
                    return Some((chunk_start, chunk_end, start, end));
                } else {
                    None
                }
            })?
        };

        // Adds `[chunk_start, start)` back to the pool.
        if chunk_start < start {
            let chunk = unsafe { &mut *(chunk as *mut Chunk) };
            chunk.size = (start - chunk_start) / PAGE_SIZE;
            unsafe { self.chunk_list.push(chunk) };
        }

        // Adds `[end, chunk_end)` back to the pool.
        if end < chunk_end {
            let new_chunk = unsafe { &mut *(end as *mut Chunk) };
            new_chunk.size = (chunk_end - end) / PAGE_SIZE;
            unsafe { self.chunk_list.push(new_chunk) };
        }

        Some(unsafe { Pages::from_raw(start as *mut RawPage, size) })
    }

    /// Frees a page back into the given page pool, making it available for reuse.
    ///
    /// This is meant to be used for freeing single pages. To free multiple pages, call
    /// `free_pages()` instead.
    pub fn free(&mut self, mut page: Page) {
        let entry = unsafe { &*(page.deref_mut() as *mut RawPage as *mut Entry) };
        mem::forget(page);
        unsafe { self.entry_list.push(entry) };
    }

    /// Frees a number of contiguous pages to the given page pool.
    pub fn free_pages(&mut self, pages: Pages) {
        let size = pages.len();
        let chunk = unsafe { &mut *(pages.into_raw() as *mut Chunk) };
        chunk.size = size;
        unsafe { self.chunk_list.push(chunk) };
    }
}

#[repr(C)]
pub struct MPool {
    pool: SpinLock<Pool>,
    fallback: *const MPool,
}

unsafe impl Sync for MPool {}

impl MPool {
    /// Initialises the given memory pool with the given entry size, which must be at least the size
    /// of two pointers.
    ///
    /// All entries stored in the memory pool will be aligned to at least the entry size.
    pub const fn new() -> Self {
        Self {
            pool: SpinLock::new(Pool::new()),
            fallback: ptr::null(),
        }
    }

    /// Initialises the given memory pool by replicating the properties of `from`. It also pulls the
    /// chunk and free lists from `from`, consuming all its resources and making them available via
    /// the new memory pool.
    pub fn new_from(from: &Self) -> Self {
        Self {
            pool: SpinLock::new(mem::replace(&mut from.pool.lock(), Pool::new())),
            fallback: from.fallback,
        }

        // TODO(@jeehoonkang): it's different from the original C implementation, where
        // `from.fallback` is re-initialized. But it seems the difference doesn't matter.
    }

    /// Initialises the given memory pool with a fallback memory pool if this pool runs out of
    /// memory.
    pub fn new_with_fallback(fallback: *const Self) -> Self {
        let mut pool = Self::new();
        pool.fallback = fallback;
        pool
    }

    /// Allocates an entry from the given memory pool, if one is available. If there isn't one
    /// available, try and allocate from the fallback if there is one.
    pub fn alloc(&self) -> Option<Page> {
        if let Some(result) = self.pool.lock().alloc() {
            return Some(result);
        }

        if let Some(fallback) = unsafe { self.fallback.as_ref() } {
            return fallback.alloc();
        }

        None
    }

    /// Allocates a number of contiguous and aligned entries. This is a best-effort operation and
    /// only succeeds if such entries can be found in the chunks list or the chunks of the fallbacks
    /// (i.e., the entry list is never used to satisfy these allocations).
    ///
    /// The alignment is specified as the number of entries, that is, if `align` is 4, the alignment
    /// in bytes will be 4 * entry_size.
    ///
    /// The caller can enventually free the returned entries by calling mpool_add_chunk.
    pub fn alloc_pages(&self, count: usize, align: usize) -> Option<Pages> {
        if let Some(result) = self.pool.lock().alloc_pages(count, align) {
            return Some(result);
        }

        if let Some(fallback) = unsafe { self.fallback.as_ref() } {
            return fallback.alloc_pages(count, align);
        }

        None
    }

    /// Frees an entry back into the memory pool, making it available for reuse.
    ///
    /// This is meant to be used for freeing single entries. To free multiple entries, one must call
    /// mpool_add_chunk instead.
    pub fn free(&self, page: Page) {
        self.pool.lock().free(page);
    }

    /// Adds a contiguous chunk of memory to the given memory pool. The chunk will eventually be
    /// broken up into entries of the size held by the memory pool.
    ///
    /// Only the portions aligned to the entry size will be added to the pool.
    ///
    /// Returns true if at least a portion of the chunk was added to pool, or false if none of the
    /// buffer was usable in the pool.
    pub fn free_pages(&self, pages: Pages) {
        self.pool.lock().free_pages(pages);
    }
}

impl Drop for MPool {
    /// Finishes the given memory pool, giving all free memory to the fallback pool if there is one.
    fn drop(&mut self) {
        if let Some(fallback) = unsafe { self.fallback.as_ref() } {
            let mut pool = self.pool.lock();
            let mut pool_fallback = fallback.pool.lock();

            unsafe {
                // Merge the freelist into the fallback.
                while let Some(entry) = pool.entry_list.pop() {
                    pool_fallback.entry_list.push(&*entry);
                }

                // Merge the chunk list into the fallback.
                while let Some(chunk) = pool.chunk_list.pop() {
                    pool_fallback.chunk_list.push(&*chunk);
                }
            }

            // TODO(@jeehoonkang): it's different from the original C implementation, where
            // `self.pool.fallback` is re-initialized. But it seems the difference doesn't matter.
        }

        // TODO(@jeehoonkang): here we're leaking all the memory chunks in this pool.
    }
}

#[no_mangle]
pub unsafe extern "C" fn mpool_enable_locks() {}

#[no_mangle]
pub unsafe extern "C" fn mpool_init(p: *mut MPool, entry_size: size_t) {
    assert_eq!(PAGE_SIZE, entry_size as usize);
    ptr::write(p, MPool::new());
}

#[no_mangle]
pub unsafe extern "C" fn mpool_init_from(p: *mut MPool, from: *mut MPool) {
    ptr::write(p, MPool::new_from(&*from));
    (*from).fallback = ptr::null();
}

#[no_mangle]
pub unsafe extern "C" fn mpool_init_with_fallback(p: *mut MPool, fallback: *const MPool) {
    ptr::write(p, MPool::new_with_fallback(fallback));
}

#[no_mangle]
pub unsafe extern "C" fn mpool_fini(p: *mut MPool) {
    ptr::drop_in_place(p);
    (*p).fallback = ptr::null();
}

#[no_mangle]
pub unsafe extern "C" fn mpool_add_chunk(p: *mut MPool, begin: *mut c_void, size: size_t) -> bool {
    Pages::from_raw_u8(begin as *mut u8, size)
        .map(|pages| (*p).free_pages(pages))
        .is_some()
}

#[no_mangle]
pub unsafe extern "C" fn mpool_alloc(p: *mut MPool) -> *mut c_void {
    (*p).alloc()
        .map(|page| page.into_raw() as *mut c_void)
        .unwrap_or_else(|| ptr::null_mut())
}

#[no_mangle]
pub unsafe extern "C" fn mpool_alloc_contiguous(
    p: *mut MPool,
    count: size_t,
    align: size_t,
) -> *mut c_void {
    (*p).alloc_pages(count as usize, align as usize)
        .map(|pages| pages.into_raw() as *mut c_void)
        .unwrap_or_else(|| ptr::null_mut())
}

#[no_mangle]
pub unsafe extern "C" fn mpool_free(p: *mut MPool, ptr: *mut c_void) {
    (*p).free(Page::from_raw(ptr as *mut RawPage));
}
