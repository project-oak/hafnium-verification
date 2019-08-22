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

use core::cell::UnsafeCell;
use core::mem;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr;
use core::sync::atomic::{spin_loop_hint, AtomicBool, Ordering};

#[repr(C)]
pub struct RawSpinLock {
    inner: AtomicBool,
}

impl RawSpinLock {
    pub const fn new() -> Self {
        Self {
            inner: AtomicBool::new(false),
        }
    }

    pub fn lock(&self) {
        while self.inner.swap(true, Ordering::Acquire) {
            spin_loop_hint();
        }
    }

    pub fn try_lock(&self) -> bool {
        !self.inner.swap(true, Ordering::Acquire)
    }

    pub fn lock_both(lhs: &Self, rhs: &Self) {
        if (lhs as *const _) < (rhs as *const _) {
            lhs.lock();
            rhs.lock();
        } else {
            rhs.lock();
            lhs.lock();
        }
    }

    pub fn unlock(&self) {
        self.inner.store(false, Ordering::Release);
    }
}

#[repr(C)]
pub struct SpinLock<T> {
    lock: RawSpinLock,
    data: UnsafeCell<T>,
}

unsafe impl<'s, T: Send> Send for SpinLock<T> {}
unsafe impl<'s, T: Send> Sync for SpinLock<T> {}

impl<T> SpinLock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            lock: RawSpinLock::new(),
            data: UnsafeCell::new(data),
        }
    }

    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }

    pub fn lock<'s>(&'s self) -> SpinLockGuard<'s, T> {
        self.lock.lock();
        SpinLockGuard {
            lock: self,
            _marker: PhantomData,
        }
    }

    pub fn try_lock<'s>(&'s self) -> Option<SpinLockGuard<'s, T>> {
        if self.lock.try_lock() {
            Some(SpinLockGuard {
                lock: self,
                _marker: PhantomData,
            })
        } else {
            None
        }
    }

    pub unsafe fn unlock_unchecked(&self) {
        self.lock.unlock();
    }

    pub unsafe fn get_unchecked(&self) -> &T {
        &*self.data.get()
    }

    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }

    pub unsafe fn get_mut_unchecked(&self) -> &mut T {
        &mut *self.data.get()
    }

    pub fn lock_both<'s>(
        lhs: &'s Self,
        rhs: &'s Self,
    ) -> (SpinLockGuard<'s, T>, SpinLockGuard<'s, T>) {
        RawSpinLock::lock_both(&lhs.lock, &rhs.lock);
        (
            SpinLockGuard {
                lock: lhs,
                _marker: PhantomData,
            },
            SpinLockGuard {
                lock: rhs,
                _marker: PhantomData,
            },
        )
    }
}

pub struct SpinLockGuard<'s, T> {
    lock: &'s SpinLock<T>,
    _marker: PhantomData<*const ()>, // !Send + !Sync
}

unsafe impl<'s, T> Send for SpinLockGuard<'s, T> {}
unsafe impl<'s, T: Send + Sync> Sync for SpinLockGuard<'s, T> {}

impl<'s, T> Drop for SpinLockGuard<'s, T> {
    fn drop(&mut self) {
        self.lock.lock.unlock();
    }
}

impl<'s, T> Deref for SpinLockGuard<'s, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'s, T> DerefMut for SpinLockGuard<'s, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'s, T> SpinLockGuard<'s, T> {
    pub unsafe fn into_raw(self) -> usize {
        let ret = self.lock as *const _ as usize;
        mem::forget(self);
        ret
    }

    pub unsafe fn from_raw(data: usize) -> Self {
        Self {
            lock: &*(data as *const _),
            _marker: PhantomData,
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn sl_init(l: *mut RawSpinLock) {
    ptr::write(l, RawSpinLock::new());
}

#[no_mangle]
pub unsafe extern "C" fn sl_lock(l: *const RawSpinLock) {
    (*l).lock();
}

#[no_mangle]
pub unsafe extern "C" fn sl_try_lock(l: *const RawSpinLock) -> bool {
    (*l).try_lock()
}

/// Locks both locks, enforcing the lowest address first ordering for locks of the same kind.
#[no_mangle]
pub unsafe extern "C" fn sl_lock_both(a: *const RawSpinLock, b: *const RawSpinLock) {
    RawSpinLock::lock_both(&*a, &*b);
}

#[no_mangle]
pub unsafe extern "C" fn sl_unlock(l: *const RawSpinLock) {
    (*l).unlock();
}
