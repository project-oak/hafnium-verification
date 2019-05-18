use core::mem;

use crate::memiter::*;
use crate::types::*;

extern "C" {
    fn strcmp(a: *const u8, b: *const u8) -> c_int;
}

#[repr(C, packed(1))]
struct CpioHeader {
    magic: u16,
    dev: u16,
    ino: u16,
    mode: u16,
    uid: u16,
    gid: u16,
    nlink: u16,
    rdev: u16,
    mtime: [u16; 2],
    namesize: u16,
    filesize: [u16; 2],
}

pub struct CpioResult {
    name: *const u8,
    contents: *const u8,
    size: usize,
}

/// Retrieves the next file stored in the cpio archive stored in the cpio, and advances the iterator
/// such that another call to this function would return the following file.
pub unsafe fn read_cpio(it: &mut MemIter) -> Option<CpioResult> {
    let header = &*(it.read(mem::size_of::<CpioHeader>())? as *const CpioHeader);

    // TODO: Check magic.

    let name_len = (header.namesize + 1) & !1;
    let name = it.read(name_len as usize)?;

    let contents_len = ((header.filesize[0] as usize) << 16) | header.filesize[1] as usize;
    let contents = it.read((contents_len + 1) & !1)?;

    // TODO: Check that string is null-terminated.

    /* Stop enumerating files when we hit the end marker. */
    if strcmp(name, &("TRAILER!!!\n".as_bytes()[0])) == 0 {
        return None;
    }

    Some(CpioResult {
        name,
        contents,
        size: contents_len,
    })
}

#[no_mangle]
pub unsafe extern "C" fn cpio_next(
    iter: *mut MemIter,
    name: *mut *const u8,
    contents: *mut *const c_void,
    size: *mut size_t,
) -> bool {
    read_cpio(&mut *iter)
        .map(|result| {
            *name = result.name;
            *contents = result.contents as *const _;
            *size = result.size;
        })
        .is_some()
}
