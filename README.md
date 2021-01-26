![](/static/marteau.jpg)

# About

Creusot is a tool for *deductive verification* of Rust code. It allows you to annotate your code with specifications, invariants and assertions and then *check* them formally, returning a *proof* your code satisfies its specification.

Creusot works by translating Rust code to WhyML the verification and specification language of ![Why3](https://why3.lri.fr). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

**Note**: I am developping this in the context of my PhD thesis, the software quality is commensurate.

# Installing

0. Install Rust using `rustup` to manage toolchains
1. Clone the repository
2. Install the Rust compiler libraries: `rustup component add rustc-dev`
3. (Optional, Recommended) Install the Rust compiler sources: `rustup component add rustc-src`
4. Run `cargo build`

# Using

```
cargo run -- path/to/file.rs
```

This command will print the MLCFG translation to STDOUT.
