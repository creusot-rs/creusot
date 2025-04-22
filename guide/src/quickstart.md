# Quickstart

## Installation

Install Creusot and why3 as described in the [README](https://github.com/creusot-rs/creusot).

## Create a project

Create a new project with this command:

```
cargo creusot new project-name
```

That command creates a directory `package-name` containing the basic elements of a Rust project verified with Creusot. The file `src/lib.rs` is initialized with an example function annotated with a contract:

```rust
// src/lib.rs
use creusot_contracts::*;

#[requires(x@ < i64::MAX@)]
#[ensures(result@ == x@ + 1)]
pub fn add_one(x: i64) -> i64 {
    x + 1
}
```

## Compile and prove

To verify this project, run this command:

```
cargo creusot prove
```

A successful run gives us the certainty that functions defined in this package satisfy their contracts:
for all arguments satisfying the preconditions (`requires` clauses), the result of the function will
satisfy the postconditions (`ensures` clauses).

### Troubleshooting

If you get an error like this

```
error: The `creusot_contracts` crate is loaded, but the following items are missing: <a list of identifiers> Maybe your version of `creusot-contracts` is wrong?
```

Add the following to your `Cargo.toml` file:

```
[patch.crates-io]
creusot-contracts = { path = "/relative/or/absolute/path/to/creusot-contracts/in/creusot/directory" }
```

And please notify the Creusot developers that the version of Creusot should be bumped to `NEXT_VERSION-dev` to prevent this error.

## Prove with Why3

Finally, launch the why3 ide:

```sh
cargo creusot why3 ide
```

The documentation for the why3 ide can be found [here](https://www.why3.org/doc/starting.html#getting-started-with-the-gui).

We also recommend section 2.3 of this [thesis](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) for a brief overview of Why3 and Creusot proofs.

We plan to improve this part of the user experience, but that will have to wait until Creusot gets more stable and complete.
If you'd like to help, a prototype VSCode plugin for Why3 is [in development](https://github.com/xldenis/whycode), it should make the experience much smoother when complete.

## Prove with Why3find

### Configure

```sh
$ cargo creusot config
```

The configuration is stored in `why3find.json`.

### Prove

1. Run the Creusot translation.

    ```sh
    $ cargo creusot
    ```

2. Run the Why3find prover.

    ```sh
    $ cargo creusot prove
    ```

    Run the Why3find prover on specific files:

    ```sh
    $ cargo creusot prove verif/[COMA_FILES]
    ```

3. Launch Why3 IDE on unproved goals (this will only open one file even if there are many listed with unproved goals).

    ```sh
    $ cargo creusot prove -i
    $ cargo creusot prove -i verif/[COMA_FILES]
    ```
