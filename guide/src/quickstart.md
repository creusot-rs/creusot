# Quickstart

Install Creusot and why3 as described in the [README](https://github.com/creusot-rs/creusot).

Then, create a new project, and import creusot-contracts to start writing specifications:

```toml
# Cargo.toml
[package]
name = "add_one"
version = "0.1.0"
edition = "2021"

[dependencies]
creusot-contracts = { path = "/PATH/TO/CREUSOT/creusot-contracts" }

```

```rust
// src/lib.rs
use creusot_contracts::*;

#[requires(x < i32::MAX)]
#[ensures(result@ == x@ + 1)]
pub fn add_one(x: i32) -> i32 {
    x + 1
}
```

Then, launch the why3 ide:

```sh
cargo creusot why3 ide
```

The documentation for the why3 ide can be found [here](https://www.why3.org/doc/starting.html#getting-started-with-the-gui).
