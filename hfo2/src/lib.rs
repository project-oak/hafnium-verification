#![no_std]
#![feature(const_fn)]
#![feature(const_panic)]
#![feature(ptr_wrapping_offset_from)]

#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate static_assertions;
extern crate reduce;
extern crate arrayvec;

mod cpio;
#[macro_use]
mod utils;
#[macro_use]
mod dlog;
mod api;
mod cpu;
mod list;
mod memiter;
mod mm;
mod mpool;
mod page;
mod panic;
mod spinlock;
mod std;
mod types;
mod vm;
