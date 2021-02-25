![](/static/marteau.jpg)

*Le marteau-pilon, forges et aciéries de Saint-Chamond, Joseph-Fortuné LAYRAUD, 1889*

# About

Creusot is a tool for *deductive verification* of Rust code. It allows you to annotate your code with specifications, invariants and assertions and then *check* them formally, returning a *proof* your code satisfies its specification.

Creusot works by translating Rust code to WhyML the verification and specification language of ![Why3](https://why3.lri.fr). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

**Note**: :warning: I am developping this in the context of my PhD thesis, the software quality is commensurate. :warning:

# Example programs that have been proven:

- [Mutably indexing a linked list](creusot/tests/should_succeed/list_index_mut.rs)
- [Zeroing out a list](creusot/tests/should_succeed/all_zero.rs)

# Installing

0. Install Rust using `rustup` to manage toolchains
1. Clone the repository
2. Install the Rust compiler libraries: `rustup component add rustc-dev`
3. (Optional, Recommended) Install the Rust compiler sources: `rustup component add rustc-src`
4. Run `cargo build`

# Generating MLCFG outputs


```
cargo run -- path/to/file.rs
```

Creusot will translate the code in this file and its dependencies, producing a file in a language called MLCFG. By default it prints this to standard out but an output file can be specified with `-o`.

# Proving programs with Why3

To actually prove programs using Why3, you will need to use a branch I am currently developing that includes the relevant support. You can find this branch here: https://gitlab.inria.fr/why3/why3/-/tree/stackify. I hope to have this branch integrated and released by 1.5.0 (though ideally earlier).

With this version of Why3, you can load your generated MLCFG in the IDE by running

```
why3 ide path/to/file.mlcfg
```

From there standard proof strategies should work. I would like to improve this part of the user experience, but that will have to wait until Creusot is more stable and complete.

# Writing specifications

Currently, writing specifications with Creusot requires a little bit of tedium. You will need to include the `creusot-contracts` crate in your project. However, since this crate is not published you will need to either load it as an `extern crate` or include a local copy in your `Cargo.toml`.

## Loading as an extern crate

To include `creusot-contracts` as an extern crate, add the appropriate declaration to your Rust file,

```
extern crate creusot_contracts;
use creusot_contracts::*;
```

Then compile your code and add `creusot-contracts` to the loadpath using the `-L` flag like so: `cargo build -L path/to/directory/with/creusot-contracts`.

:warning: Currently `creusot-contracts` is very unfinished, using the macros included in this crate may prevent your Rust code from compiling normally, I still need to implement a pass-through mode for normal compilation. :warning:

## Kinds of contract expressions

Currently Creusot uses 4 different kinds of contract expressions. The most basic are `requires` and `ensures` which can be attached to a Rust function declaration like so:

```rust
#[requires(R)]
#[ensures(E)]
fn my_function(b: u32) -> bool { .. }
```

You can attach as many `ensures` and `requires` clauses as you would like, in any order.

Inside a function, you can attach `invariant` clauses to loops, these are attached on _top_ of the loop rather than inside, that is:

```
#[invariant(name, E)]
while true {}
```

Invariants must have names (for now).

Finally, there is a `variant` expression which may be useful when defining _logical functions_ where it is required to prove termination. You can give it an expression as argument, that expression must form a well-founded order which strictly decreases at each recursive call.

## Pearlite

Contracts and logic functions are written in Pearlite, a specification language for Rust I am developing. Pearlite can be seen as a pure, immutable fragment of Rust which has access to a few additional logical operations and connectors. In practice you have:

- Base Rust expressions: matching, function calls, let bindings, binary and unary operators, tuples, structs and enums, projections, primitive casts, and dereferencing.
- Logical Expressions: quantifiers (`forall` and `exists`), logical implication `->`, _logical_ equality `≡` /`===`, labels
- Rust specific logical expressions: Access to the **final** value of a mutable borrow! `^` /`@fin`

You also have two new kinds of declarations: `logic` and `hybrid`

When a function is annotated with `logic`, its body will be treated as a pearlite expression, this means that you can use quantifiers, have access to final values of borrows and all the goodies. However, you cannot call this function in normal Rust code, currently this is enforced by replacing the body with a `panic!`.

The second kind of declaration `hybrid` (not yet implemented), allows you to mark a Rust function as both a logic function and a program function. This means your code must lie in the intersection of these languages. In particular this means no mutation of any kind (even recursively) and no quantifiers or logic specific constructs.
