# Quickstart

## Installation

Install Creusot and why3 as described in the [README](https://github.com/creusot-rs/creusot).

## Write specifications

Create a new project, and import creusot-contracts to start writing specifications:

```toml
# Cargo.toml
[package]
name = "add_one"
version = "0.1.0"
edition = "2021"

[dependencies]
creusot-contracts = { path = "/PATH/TO/CREUSOT/creusot-contracts" }
```

**Remark** This may only work if you're using the same rust toolchain that was used to build `creusot`:
you can copy the [`rust-toolchain`](https://github.com/creusot-rs/creusot/blob/master/ci/rust-toolchain) file into the root of your project to
make sure the correct toolchain is selected.

Then you can start writing specifications:

```rust
// src/lib.rs
use creusot_contracts::*;

#[requires(x < i32::MAX)]
#[ensures(result@ == x@ + 1)]
pub fn add_one(x: i32) -> i32 {
    x + 1
}
```

## Prove with Why3

Finally, launch the why3 ide:

```sh
cargo creusot why3 ide
```

The documentation for the why3 ide can be found [here](https://www.why3.org/doc/starting.html#getting-started-with-the-gui).

We also recommend section 2.3 of this [thesis](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) for a brief overview of Why3 and Creusot proofs.

We plan to improve this part of the user experience, but that will have to wait until Creusot gets more stable and complete.
If you'd like to help, a prototype VSCode plugin for Why3 is [in development](https://github.com/xldenis/whycode), it should make the experience much smoother when complete.
