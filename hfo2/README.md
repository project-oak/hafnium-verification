# HfO₂: Hafnium Oxide

## Installation

- Install `rustup`.

- `rustup component add rust-src rustfmt`

- `cargo install cargo-xbuild`

## Build

Run `make` in the root `hafnium` directory.

## Measure unsafe expressions and functions, etc.

Use [cargo-osha][osha]. You can run like this:

 - `git clone https://github.com/icefoxen/cargo-osha`
 - `cd cargo-osha`
 - `cargo run -- PATH_TO_HFO2/src/*.rs`

The result will exclude arch-dependent code.

[osha]: https://github.com/icefoxen/cargo-osha
