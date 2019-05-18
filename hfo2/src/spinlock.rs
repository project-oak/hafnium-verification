use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::sync::atomic::{AtomicBool, Ordering};

pub struct SpinLock {
    inner: AtomicBool,
}

impl SpinLock {
    pub const fn new() -> Self {
        Self {
            inner: AtomicBool::new(false),
        }
    }

    fn lock<'s>(&'s self) -> Guard<'s> {
        while self.inner.swap(true, Ordering::Acquire) {}
        Guard {
            lock: self,
            _marker: PhantomData,
        }
    }

    fn lock_both<'s>(lhs: &'s Self, rhs: &'s Self) -> (Guard<'s>, Guard<'s>) {
        if lhs as *const _ < rhs as *const _ {
            let l = lhs.lock();
            let r = rhs.lock();
            (l, r)
        } else {
            let r = rhs.lock();
            let l = lhs.lock();
            (l, r)
        }
    }
}

pub struct Guard<'s> {
    lock: *const SpinLock,
    _marker: PhantomData<(*const (), &'s SpinLock)>, // !Send + !Sync
}

impl<'s> Drop for Guard<'s> {
    fn drop(&mut self) {
        let lock = unsafe { &*self.lock };
        lock.inner.store(false, Ordering::Release);
    }
}

#[no_mangle]
pub unsafe extern "C" fn sl_init(l: *mut SpinLock) {
    ptr::write(l, SpinLock::new());
}

#[no_mangle]
pub unsafe extern "C" fn sl_lock(l: *const SpinLock) {
    mem::forget((*l).lock());
}

/// Locks both locks, enforcing the lowest address first ordering for locks of the same kind.
#[no_mangle]
pub unsafe extern "C" fn sl_lock_both(a: *const SpinLock, b: *const SpinLock) {
    mem::forget(SpinLock::lock_both(&*a, &*b));
}

#[no_mangle]
pub unsafe extern "C" fn sl_unlock(l: *const SpinLock) {
    drop(Guard {
        lock: l,
        _marker: PhantomData,
    });
}
