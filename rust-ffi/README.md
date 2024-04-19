# RustFFI bindings for Arkworks library

Relevant links:

1. https://github.com/yvan-sraka/cargo-cabal
2. https://github.com/yvan-sraka/hs-bindgen-types#
3. https://github.com/orgs/arkworks-rs/repositories

## Setup

1. Install [Rust](https://www.rust-lang.org/tools/install) and update to latest stable release

```bash
rustup update
```

## Build Rust library and test

```bash
cd rust-ffi
cargo build
cargo test
```

## Build Haskel and run test

```bash
cabal build rust-ffi
cabal run rust-ffi-test
```
