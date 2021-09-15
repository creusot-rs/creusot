![](/static/marteau.jpg)

*Le marteau-pilon, forges et aciéries de Saint-Chamond, Joseph-Fortuné LAYRAUD, 1889*

# About

Creusot is a tool for *deductive verification* of Rust code. It allows you to annotate your code with specifications, invariants and assertions and then *check* them formally, returning a *proof* your code satisfies its specification.

Creusot works by translating Rust code to WhyML the verification and specification language of ![Why3](https://why3.lri.fr). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

See [ARCHITECTURE.md](ARCHITECTURE.md) for technical details!

**Note**: :warning: This tool is mainly for research purposes now. Please tolerate the software quality! :warning:

# Examples of Verification

- [Mutably indexing a linked list](creusot/tests/should_succeed/list_index_mut.rs)
- [Zeroing out a list](creusot/tests/should_succeed/all_zero.rs)
- [Binary search](creusot/tests/should_succeed/binary_search.rs)

More examples are found in [creusot/tests/should_succeed](creusot/tests/should_succeed).

# Installing

0. Clone the [creusot](https://github.com/xldenis/creusot/) repo, set the current directory to that folder
1. Set up Rust
    - [Install `rustup`](https://www.rust-lang.org/tools/install), to get suitable Rust toolchains
    - Make sure you are at the repo dir (so that rustup can load [`rust-toolchain`](rust-toolchain))
    - Install the basic toolchain: `$ rustup component add rustc-dev`
    - (Optional, Recommended) Also install the Rust compiler sources: `$ rustup component add rustc-src`
2. Fully build Creusot
    - Build basic parts: `$ cargo build`
    - Fully initialize by performing tests: `$ cargo test` (TODO: better initialization)
3. Get Why3
    - [Get `opam`](https://opam.ocaml.org/doc/Install.html), the package manager for OCaml
    - Specify the [`stackify` branch](https://gitlab.inria.fr/why3/why3/-/tree/stackify) for `why3`: `$ opam pin add why3 https://gitlab.inria.fr/why3/why3.git#stackify`
    - Install `why3` and `why3-ide`: `$ opam install why3 why3-ide`
    - Get some SMT solvers:
      [Z3](https://github.com/Z3Prover/z3) (available by `brew`, `apt`, etc.),
      [CVC4](https://cvc4.github.io/) (`brew`, `apt`, etc.),
      [Alt-Ergo](https://alt-ergo.ocamlpro.com/) (`opam`, `apt`, etc.)
    - Configure Why3: `$ why3 config detect`

# Verifying with Creusot and Why3

## Turning to MLCFG

Creusot can translate the Rust programs into a language supported by Why3, called MLCFG (Call flow graph for OCaml).

By running the following, you can have Creusot turn a Rust program to a MLCFG (assuming that you are in the repo dir).
```
cargo run --bin creusot-rustc -- -Zno-codegen --extern creusot_contracts=./creusot/target/debug/libcreusot_contracts.rlib -Ldependency=./creusot/target/debug/deps/ PATH/TO/PROGRAM.rs
```
(You can play with examples in [creusot/tests/should_succeed](creusot/tests/should_succeed).)

By default the output MLCFG goes to stdout, but you can also specify the output file with `-o PATH/TO/OUTPUT.mlcfg`
(file extension is not relevant to Why3).

## Proving in Why3

First, in order to process MLCFG outputs by Creusot, you need the [`stackify` branch](https://gitlab.inria.fr/why3/why3/-/tree/stackify) version of Why3, as mentioned in the Installing section. We hope to have this branch integrated and released by 1.5.0 (or ideally earlier).

Now, let's have Why3 process verification conditions of your MLCFG.

You can run the following to call Why3 with the SMT solver Z3 (assuming that you are at the repo dir).
```
why3 prove -L ./prelude -P z3 PATH/TO/OUTPUT.mlcfg
```
You can also change `z3` to `cvc4` or `alt-ergo`.

You can also run Why3 IDE to view more information or do interactive proofs. You can run the following (assuming that you are at the repo dir).
```
why3 ide -L ./prelude PATH/TO/OUTPUT.mlcfg
```
From there standard proof strategies of Why3 work.

We plan to improve this part of the user experience, but that will have to wait until Creusot gets more stable and complete.

# Writing specs in Rust programs

Currently, writing specifications with Creusot requires a little bit of tedium.

## Using the `creusot-contracts` crate

First, you will need to depend on the `creusot-contracts` crate. However, since this crate is not published currently. To use it for your own Rust project, you need to either load it as an `extern crate` or include a local copy in your `Cargo.toml`.

To include `creusot-contracts` as an extern crate, add the appropriate declaration to your Rust file,

```
extern crate creusot_contracts;
use creusot_contracts::*;
```

Then compile your code and add `creusot-contracts` to the loadpath using the `-L` flag like so: `cargo build -L path/to/directory/with/creusot-contracts`.

:warning: Currently `creusot-contracts` is very unfinished, using the macros included in this crate may prevent your Rust code from compiling normally, we still need to implement a pass-through mode for normal compilation. :warning:

## Kinds of contract expressions

Currently Creusot uses 4 different kinds of contract expressions. The most basic are `requires` and `ensures` which can be attached to a Rust function declaration like so:

```rust
#[requires(... precondition ...)]
#[ensures(... postcondition ...)]
fn my_function(i: u32) -> bool { ... }
```

You can attach as many `ensures` and `requires` clauses as you would like, in any order.

Inside a function, you can attach `invariant` clauses to loops, these are attached on _top_ of the loop rather than inside, that is:
```rust
#[invariant(invariant_name, ... loop invariant ...)]
while ... { ... }
```
Invariants must have names (for now).

Finally, there is a `variant` expression which may be useful when defining *logical functions* where it is required to prove termination. You can give it an expression as argument, that expression must form a well-founded order which strictly decreases at each recursive call.

## Pearlite

Contracts and logic functions are written in Pearlite, a specification language for Rust we are developing. Pearlite can be seen as a pure, immutable fragment of Rust which has access to a few additional logical operations and connectives. In practice you have:

- Base Rust expressions: matching, function calls, let bindings, binary and unary operators, tuples, structs and enums, projections, primitive casts, and dereferencing.
- Logical Expressions: quantifiers (`forall` and `exists`), logical implication `->`, *logical* equality `≡` /`===`, labels
- Rust specific logical expressions: Access to the **final** value of a mutable borrow! `^` /`@fin`

You also have two new kinds of declarations: `logic` and `hybrid`.

When a function is annotated with `logic`, its body will be treated as a pearlite expression, this means that you can use quantifiers, have access to final values of borrows and all the goodies. However, you cannot call this function in normal Rust code, currently this is enforced by replacing the body with a `panic!`.

The second kind of declaration `hybrid` (not yet implemented), allows you to mark a Rust function as both a logic function and a program function. This means your code must lie in the intersection of these languages. In particular this means no mutation of any kind (even recursively) and no quantifiers or logic specific constructs.
