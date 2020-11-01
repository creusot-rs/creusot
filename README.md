![](/static/marteau.jpg)

# Installing

0. Install Rust using `rustup` to manage toolchains
1. Clone the repository
2. Install the Rust compiler libraries: `rustup component add rustc-dev`
3. (Optional, Recommended) Install the Rust compiler sources: `rustup component add rustc-src`
4. Run `cargo build`

# Using

To use `creusot` you must point it at the sysroot for the toolchain you built with.
Usually this should be `$HOME/.multirust/toolchains/<toolchain>/lib/rustlib/x86_64-apple-darwin/lib/`.
You can then compile a Rust source file by running:

```
cargo run -- -L $HOME/.multirust/toolchains/<toolchain>/lib/rustlib/x86_64-apple-darwin/lib/ path/to/file.rs
```

This command will print the MLCFG translation to STDOUT.
