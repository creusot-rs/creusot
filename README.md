![](/static/marteau.jpg)

*Le marteau-pilon, forges et aciéries de Saint-Chamond, Joseph-Fortuné LAYRAUD, 1889*

# About

Creusot is a tool for *deductive verification* of Rust code. It allows you to annotate your code with specifications, invariants and assertions and then *verify* them formally and automatically, returning a *proof* that your code satisfies the specs.

Creusot works by translating Rust code to WhyML, the verification and specification language of [Why3](https://why3.lri.fr). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

See [ARCHITECTURE.md](ARCHITECTURE.md) for technical details.

**Note**: :warning: This tool is mainly for research purposes now. Please tolerate the software quality! :warning:

# Examples of Verification

- [Mutably indexing a linked list](creusot/tests/should_succeed/list_index_mut.rs)
- [Zeroing out a list](creusot/tests/should_succeed/all_zero.rs)
- [Binary search](creusot/tests/should_succeed/binary_search.rs)

More examples are found in [creusot/tests/should_succeed](creusot/tests/should_succeed).

# Installing

0. Clone the [creusot](https://github.com/xldenis/creusot/) repo at any directory you like
    - Below, we write `REPO` for the (relative or absolute) path to the directory of the repo
1. Set up **Rust**
    - [Install `rustup`](https://www.rust-lang.org/tools/install), to get the suitable Rust toolchain
2. Build **Creusot**
    - Run `$ REPO/build`
3. Set up **Why3**
    - [Get `opam`](https://opam.ocaml.org/doc/Install.html), the package manager for OCaml
    - Specify the [`stackify` branch](https://gitlab.inria.fr/why3/why3/-/tree/stackify) for `why3`: `$ opam pin add why3 https://gitlab.inria.fr/why3/why3.git#stackify`
    - Install `why3` and `why3-ide`: `$ opam install why3 why3-ide`
    - Get some SMT solvers: [Z3](https://github.com/Z3Prover/z3) (available by `brew`, `apt`, etc.), [CVC4](https://cvc4.github.io/) (`brew`, `apt`, etc.), [Alt-Ergo](https://alt-ergo.ocamlpro.com/) (`opam`, `apt`, etc.)
    - Configure Why3: `$ why3 config detect`
      * Troubleshoot:
        When your `z3` is a bit too new (e.g., Why3 supports up to ver. 4.8.10 but yours is 4.8.12), Why3 refuses `z3`.
        Then you can try hacking Why3 to make it consider your `z3` be of an older version (e.g., 4.8.10), by updating the relevant field of `~/.why3.conf`.

# Verifying with Creusot and Why3

## Turning to MLCFG

Creusot can translate the Rust programs into a language supported by Why3, called MLCFG (a call flow graph for ML, more specifically WhyML).

By running the following, you can have Creusot turn a Rust program to a MLCFG.
```
REPO/mlcfg PATH/TO/PROGRAM.rs -o PATH/TO/OUTPUT.mlcfg
```
If you omit the `-o ...` part, it outputs MLCFG to stdout.
(The file extension of MLCFG is not relevant to Why3.)

You can play with examples in [creusot/tests/should_succeed](creusot/tests/should_succeed).
(There we have `*.stdout` files for the MLCFG outputs.)

Later we show how to write Rust programs with specs for Creusot.

## Proving in Why3

First, in order to process MLCFG outputs by Creusot, you need the [`stackify` branch](https://gitlab.inria.fr/why3/why3/-/tree/stackify) version of Why3, as mentioned in the Installing section. We hope to have this branch integrated and released by 1.5.0 (or ideally earlier).

Now, let's have Why3 process verification conditions of your MLCFG.

You can run the following to call Why3 with the SMT solver Z3 (assuming that you are at the repo dir).
```
REPO/prove -P z3 PATH/TO/OUTPUT.mlcfg
```
You can also change `z3` to `cvc4` or `alt-ergo`.
(`REPO/prove` is a thin wrapper of `why3 prove`.)

You can also run Why3 IDE to view more information or do interactive proofs. You can run the following (assuming that you are at the repo dir).
```
REPO/ide PATH/TO/OUTPUT.mlcfg
```
From there standard proof strategies of Why3 work.

We plan to improve this part of the user experience, but that will have to wait until Creusot gets more stable and complete.

# Writing specs in Rust programs

## Using the `creusot-contracts` crate

First, you will need to depend on the `creusot-contracts` crate. However, since this crate is not published currently. To use it for your own Rust project, you need to either load it as an `extern crate` or include a local copy in your `Cargo.toml`.

To include `creusot-contracts` as an extern crate, add a declaration to your Rust project like the following:
```
extern crate creusot_contracts;
use creusot_contracts::*;
```

Then compile your code and add `creusot-contracts` to the loadpath using the `-L` flag like so: `cargo build -L PATH/TO/creusot-contracts`.

:warning: Currently `creusot-contracts` is very unfinished. Using the macros included in this crate may prevent your Rust code from compiling normally. (TODO: implement a pass-through mode for normal compilation) :warning:

## Kinds of contract expressions

Currently Creusot uses 4 different kinds of contract expressions.

The most basic are `requires` and `ensures`, which can be attached to a Rust function declaration like so:
```rust
#[requires(... precondition ...)]
#[ensures(... postcondition ...)]
fn my_function(i: u32) -> bool { ... }
```
You can attach as many `ensures` and `requires` clauses as you would like, in any order.

Inside a function, you can attach `invariant` clauses to loops, these are attached on *top* of the loop rather than inside, like:
```rust
#[invariant(invariant_name, ... loop invariant ...)]
while ... { ... }
```
Invariants must have names (for now).

Finally, there is a `variant` expression, which may be useful when defining *logical functions*, whose termination must be proved. You can give it an expression as argument, whose values must strictly decrease (in a known well-founded order) at each recursive call.

## Pearlite

Contracts and logic functions are written in Pearlite, a specification language for Rust we are developing. Pearlite can be seen as a pure, immutable fragment of Rust which has access to a few additional logical operations and connectives. In practice you have:

- Base Rust expressions: matching, function calls, let bindings, binary and unary operators, tuples, structs and enums, projections, primitive casts, and dereferencing.
- Logical Expressions: quantifiers (`forall` and `exists`), logical implication `->`, *logical* equality `equal(a, b)` (TODO: add `a ≡ b` / `a === b`), labels
- Rust specific logical expressions: access to the **final** value of a mutable borrow! `^` /`@fin`

You also have two new kinds of declarations: `logic` and `hybrid`.

When a function is annotated with `logic`, its body will be treated as a pearlite expression. This means that you can use quantifiers, have access to final values of borrows, and all the goodies. However, you cannot call this function in normal Rust code (currently this is enforced by replacing the body with a `panic!`).

The second kind of declaration is `hybrid` (sorry, not yet implemented) (TODO: implement it). It allows you to mark a Rust function as both a logic function and a program function. This means your code must lie in the intersection of these languages. In particular this means no mutation of any kind (even recursively) and no quantifiers or logic specific constructs.
