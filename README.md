![](/static/marteau.jpg)

*Le marteau-pilon, forges et aciéries de Saint-Chamond, Joseph-Fortuné LAYRAUD, 1889*

----

📢 Are you interested in verifying Rust code? Don't know where to start? Please contact me, I'm always looking for case-studies. 📢

----

# About

**Creusot** is a tool for *deductive verification* of Rust code. It allows you to annotate your code with specifications, invariants and assertions and then *verify* them formally and automatically, *proving*, mathematically, that your code satisfies your specifications.

Creusot works by translating Rust code to WhyML, the verification and specification language of [Why3](https://why3.lri.fr). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

See [ARCHITECTURE.md](ARCHITECTURE.md) for technical details.

:warning: This is _research_ software, and favors _progress_ over stability :warning:

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

. Set up **Rust**
    - [Install `rustup`](https://www.rust-lang.org/tools/install), to get the suitable Rust toolchain
1. Set up **Why3**
    - [Get `opam`](https://opam.ocaml.org/doc/Install.html), the package manager for OCaml
    - Pin `why3` to `master` : 
    ```
    $ opam pin add why3 https://gitlab.inria.fr/why3/why3.git
    $ opam pin add why3-ide https://gitlab.inria.fr/why3/why3.git
    ```
    - Install `why3` and `why3-ide`: `$ opam install lablgtk3 lablgtk3-sourceview3 ocamlgraph why3 why3-ide`
    - Get some SMT solvers: [Z3](https://github.com/Z3Prover/z3) (available by `brew`, `apt`, etc.), [CVC4](https://cvc4.github.io/) (`brew`, `apt`, etc.), [Alt-Ergo](https://alt-ergo.ocamlpro.com/) (`opam`, `apt`, etc.)
    - Configure Why3: `$ why3 config detect`
      * Troubleshoot:
        When your `z3` is a bit too new (e.g., Why3 supports up to ver. 4.8.10 but yours is 4.8.12), Why3 refuses `z3`.
        Then you can try hacking Why3 to make it consider your `z3` be of an older version (e.g., 4.8.10), by updating the relevant field of `~/.why3.conf`.
2. Clone the [creusot](https://github.com/xldenis/creusot/) repo at any directory you like
3. Build **Creusot**
    - Enter the cloned directory and run `$ cargo install --path creusot`, this will build the `cargo-creusot` and `creusot-rustc` executables and place them in `~/.cargo/bin`.


# Verifying with Creusot and Why3

The recommended way for users to verify programs with Creusot is to use `cargo-creusot`.
All you need to do is enter your project and run `cargo creusot`!
This will generate MLCFG files in `target/debug/` which can then be loaded into Why3.

This may only work if you're using the same rust toolchain that was used to build `creusot`:
you can copy the [`rust-toolchain`](./rust-toolchain) file into the root of your project to
make sure the correct toolchain is selected.

To add contracts to your programs you will need to use the `creusot-contracts` crate by adding it as a dependency:
```toml
# Cargo.toml

[dependencies]
creusot-contracts = { path = "/path/to/creusot/creusot-contracts" }
```
and enabling the `contracts` feature through running with `cargo creusot -- --features=contracts`.
When that feature is enabled `rustc` cannot successfully compile your programs, so we recommend adding a feature to your program which conditionally enables the `contracts` feature like so:

```toml
# Cargo.toml

[features]
contracts = ["creusot-contracts/contracts"]
```

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
#[invariant(invariant_name, ... loop invariant ...)]
while ... { ... }
```
Invariants must have names (for now).

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
Marked  `#[logic]` or `#[predicate]`, a function can be used in specs and other logical conditions (`requires`/`ensures` and `invariant`).
The two attributes have the following difference.
- A `logic` function can freely have logical, non-executable operations, such as quantifiers, logic equalities, etc. Instead, this function can't be called in normal Rust code (the function body of a `logic` function is replaced with a panic).
  You can use pearlite syntax for any part in the logic function by marking that part with the `pearlite! { ... }` macro.
- A `predicate` is a logical function which returns a proposition (in practice, returns a boolean value).

When you write *recursive* `logic` or `predicate` functions, you have to show that the function terminates.
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
