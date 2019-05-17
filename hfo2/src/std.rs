use crate::types::*;

extern "C" {
    fn memset(s: *const c_void, c: c_int, n: size_t) -> *const c_void;
}

#[no_mangle]
pub extern "C" fn memset_s(dest: *const c_void, destsz: size_t, ch: c_int, count: size_t) {
    if dest.is_null() || destsz > RSIZE_MAX || count > RSIZE_MAX || count > destsz {
        panic!("memset_s failure");
    }

    unsafe {
        memset(dest, ch, count);
    }
}
