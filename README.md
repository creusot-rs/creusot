![](/static/marteau.jpg)

*Le marteau-pilon, forges et aciéries de Saint-Chamond, Joseph-Fortuné LAYRAUD, 1889*

# About

**Creusot** is a *deductive verifier* for Rust code. It verifies your code is safe from panics, overflows, and assertion failures. By adding annotations you can take it further and verify your code does the *correct* thing.

Creusot works by translating Rust code to WhyML, the verification and specification language of [Why3](https://why3.lri.fr). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

See [ARCHITECTURE.md](ARCHITECTURE.md) for technical details.

## Citing Creusot

If you would like to cite Creusot in academic contexts, we encourage you to use our [ICFEM'22 publication](https://hal.inria.fr/hal-03737878/file/main.pdf).

# Examples of Verification

To get an idea of what verifying a program with Creusot looks like, we encourage you to take a look at some of our test suite:

- [Zeroing out a vector](creusot/tests/should_succeed/vector/01.rs)
- [Binary search on Vectors](creusot/tests/should_succeed/vector/04_binary_search.rs)
- [Sorting a vector](creusot/tests/should_succeed/vector/02_gnome.rs)
- [IterMut](creusot/tests/should_succeed/iterators/02_iter_mut.rs)
- [Normalizing If-Then-Else Expressions](creusot/tests/should_succeed/ite_normalize.rs)

More examples are found in [creusot/tests/should_succeed](creusot/tests/should_succeed).

## Projects built with Creusot

- [CreuSAT](https://github.com/sarsko/creusat) is a verified SAT solver written in Rust and verified with Creusot. It really pushes the tool to its limits and gives an idea of what 'use in anger' looks like.
- Another big project is in the works :)

# Installing Creusot as a user

1. Set up **Rust**
    - [Install `rustup`](https://www.rust-lang.org/tools/install), to get the suitable Rust toolchain
2. Clone the [creusot](https://github.com/creusot-rs/creusot/) repo at any directory you like
3. Set up **Why3** and **Alt-Ergo**
   - [Get `opam`](https://opam.ocaml.org/doc/Install.html), the package manager for OCaml
   - Enter the cloned Creusot directory and create a local `opam` switch with why3 and alt-ergo:
   ```
   $ opam switch create -y . ocaml.4.14.1
   $ eval $(opam env)
   ```
   This will build why3, alt-ergo and their ocaml dependencies in a local `_opam` directory.
4. Build **Creusot**
    - In the cloned Creusot directory, run:
    ```
    $ cargo install --path creusot-rustc
    $ cargo install --path cargo-creusot
    ```
    this will build the `cargo-creusot` and `creusot-rustc` executables and place them in `~/.cargo/bin`.
5. Set up **Creusot**
   ```
   $ cargo creusot setup install
   ```
   This will download additional solvers (Z3, CVC4, CVC5) and configure Why3 to use them.

# Upgrading Creusot 

1. Enter the cloned Creusot git repository used previously to install Creusot
2. Update Creusot's sources:
   ```
   $ git pull
   ```
2. Upgrade Why3 and Alt-Ergo if needed:
   ```
   $ eval $(opam env)
   $ opam update
   $ opam install .
   ```
3. Rebuild and reinstall Creusot:
   ```
   $ cargo install --path creusot-rustc
   $ cargo install --path cargo-creusot
   ```
4. Re-run Creusot's setup:
   ```
   $ cargo creusot setup install
   ```

# Hacking on Creusot

See [HACKING.md](HACKING.md) for information on the developer workflow for
hacking on the Creusot codebase.

# Verifying with Creusot and Why3

The recommended way for users to verify programs with Creusot is to use `cargo-creusot`.
All you need to do is enter your project and run `cargo creusot`!
This will generate MLCFG files in `target/debug/` which can then be loaded into Why3.

This may only work if you're using the same rust toolchain that was used to build `creusot`:
you can copy the [`rust-toolchain`](./ci/rust-toolchain) file into the root of your project to
make sure the correct toolchain is selected.

To add contracts to your programs you will need to use the `creusot-contracts` crate by adding it as a dependency:
```toml
# Cargo.toml

[dependencies]
creusot-contracts = { path = "/path/to/creusot/creusot-contracts" }
```

Adding this dependency will make the contract macros available in your code. These macros will erase themselves when compiled with `rustc`.
To add Creusot-only trait implementations or code, you can use `cfg(creusot)` to toggle.

You must also explicitly use the `creusot_contracts` crate in your code (which should be the case once you actually prove things, but not necessarily when you initially set up a project), such as with the line:

```rust
use creusot_contracts::*;
```

or you will get a compilation error complaining that the `creusot_contracts` crate is not loaded.

## Proving in Why3

To load your files in Why3, we recommend using the [`ide`](./ide) script provided in the Creusot repository.
You may also copy both this script and the `prelude` directory in your project to have a fully self contained proof environment.

To load your proofs in Why3, run:

```
REPO/ide PATH/TO/OUTPUT.mlcfg
```

From there standard proof strategies of Why3 work. We recommend section 2.3 of this [thesis](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) for a brief overview of Why3 and Creusot proofs.

We plan to improve this part of the user experience, but that will have to wait until Creusot gets more stable and complete.
If you'd like to help, a prototype VSCode plugin for Why3 is [in development](https://github.com/xldenis/whycode), it should make the experience much smoother when complete.

# Writing specs in Rust programs

## Using Creusot for your Rust code

First, you will need to depend on the `creusot-contracts` crate, add it to your `Cargo.toml` and enable the `contracts` feature to turn on contracts.

## Kinds of contract expressions

Currently Creusot uses 4 different kinds of contract expressions: `requires`, `ensures`, `invariant` and `variant`.

The most basic are `requires` and `ensures`, which can be attached to a Rust function declaration like so:
```rust
#[requires(... precondition ...)]
#[ensures(... postcondition ...)]
fn my_function(i: u32) -> bool { ... }
```
You can attach as many `ensures` and `requires` clauses as you would like, in any order.

Inside a function, you can attach `invariant` clauses to loops, these are attached on *top* of the loop rather than inside, like:
```rust
#[invariant(... loop invariant ...)]
while ... { ... }
```

A `variant` clause can be attached either to a function like `ensures`, or `requires` or to a loop like `invariant`, it should contain a strictly decreasing expression which can prove the termination of the item it is attached to.

## Controlling verification

We also have features for controlling verification.

First, the `trusted` marker lets Creusot trust the implementation and specs.
More specifically, you can put `#[trusted]` on a function like the following:
```rust
#[trusted]
#[ensures(result == 42u32)]
fn the_answer() -> u32 {
  trusted_super_oracle("the answer to life, the universe and everything")
}
```

Causing Creusot to assume the contracts are true.

### Unbounded integers

By default in Creusot, integers are represented with bounds-checking. This can be tedious or difficult to prove in certain cases, so we can disable bounds checking by passing the `--unbounded` flag to Creusot.


## Pearlite

Contracts and logic functions are written in Pearlite, a specification language for Rust we are developing. Pearlite can be seen as a pure, immutable fragment of Rust which has access to a few additional logical operations and connectives. In practice you have:
- Base Rust expressions: matching, function calls, let bindings, binary and unary operators, tuples, structs and enums, projections, primitive casts, and dereferencing
- Logical Expressions: quantifiers (`forall` and `exists`), logical implication `==>`, *logical* equality `a == b`, labels
- Rust specific logical expressions: access to the **final** value of a mutable reference `^`, access to the *model* of an object `@`

We also provide two new attributes on Rust functions: `logic` and `predicate`.

Marked  `#[logic]` or `#[predicate]`, a function can be used in specs and other logical conditions (`requires`/`ensures` and `invariant`). They can use ghost functions.
The two attributes have the following difference.
- A `logic` function can freely have logical, non-executable operations, such as quantifiers, logic equalities, etc. Instead, this function can't be called in normal Rust code (the function body of a `logic` function is replaced with a panic).
  You can use pearlite syntax for any part in the logic function by marking that part with the `pearlite! { ... }` macro.

  If you need to use the prophecy operator `^` on a mutable reference, you need to mark the function `#[logic(prophetic)]`.
- A `predicate` is a logical function which returns a proposition (in practice, returns a boolean value).

When you write *recursive* `ghost`, `logic` or `predicate` functions, you have to show that the function terminates.
For that, you can add `#[variant(EXPR)]` attribute, which says that the value of the expression `EXPR` strictly decreases (in a known well-founded order) at each recursive call.
The type of `EXPR` should implement the `WellFounded` trait.

You can also give a custom *model* to your type.
To do that, you just implement the `Model` trait (provided in `creusot_contracts`) specifying the associated type `Model`.
You give a trusted spec that defines the model (which can be accessed by `@`) on primitive functions.
For example, the following gives a spooky data type `MyPair<T, U>` a nice pair model.
```rust
impl<T, U> Model for MyPair<T, U> {
    type Target = (T, U);
}
#[trusted]
#[ensures(@result == (a, b))]
fn my_pair<T, U>(a: T, b: U) -> MyPair<T, U> {
  ...
}
```
