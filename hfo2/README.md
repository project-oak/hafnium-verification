# HfO₂: Hafnium Oxide

## Installation

- Install `rustup`.

- `rustup component add rust-src rustfmt`

- `cargo install cargo-xbuild`

## Build

Run `make` in the root `hafnium` directory.

## Measure `unsafe`

Use [cargo-count][count]. You can run like this:

 - `cargo install cargo-count`
 - `cargo count -e arch --unsafe-statistics`

The result will exclude arch-dependent code.

[count]: https://github.com/kbknapp/cargo-count
