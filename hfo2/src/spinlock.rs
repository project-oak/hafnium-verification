use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::mem;
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

    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
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

#[no_mangle]
pub unsafe extern "C" fn sl_init(l: *mut RawSpinLock) {
    ptr::write(l, RawSpinLock::new());
}

#[no_mangle]
pub unsafe extern "C" fn sl_lock(l: *const RawSpinLock) {
    (*l).lock();
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
