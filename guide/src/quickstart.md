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

```sh
cargo creusot prove
```

A successful run gives us the certainty that functions defined in this package satisfy their contracts:
for all arguments satisfying the preconditions (`requires` clauses), the result of the function will
satisfy the postconditions (`ensures` clauses).

The command `cargo creusot prove` does two things: compile your Rust crate to Coma, then search for
proofs of verification conditions generated from the Coma code using Why3find. These steps can be performed separately.

1. Run only the compiler and obtain Coma code:

    ```sh
    cargo creusot
    ```

2. Run Why3find's proof search only on a specific Coma file (by default, Why3find is run on all Coma files under the `verif`):

    ```sh
    cargo creusot prove verif/[COMA_FILE]
    ```

    Multiple files can also be specified in a single command.

When the proof fails, you can add the `-i` option to open the Coma file in Why3 IDE.

```sh
cargo creusot prove -i verif/[COMA_FILE]
```

The `-i` option only launches the Why3 IDE if the proof fails. The following command opens Why3 IDE even if the proof succeeds:

```sh
cargo creusot why3 ide verif/[COMA_FILE]
```

When you know that the proof is going to fail, it can be slow to update every time you modify your code.
To skip proof search and just reuse the existing `proof.json` as is, add the option `--with-proof replay`.

The documentation for the Why3 IDE can be found [here](https://www.why3.org/doc/starting.html#getting-started-with-the-gui).

We also recommend section 2.3 of this [thesis](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) for a brief overview of Why3 and Creusot proofs.

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

## Legacy workflow with Why3 IDE

Run the Creusot compiler:

```sh
cargo creusot
```

Launch the Why3 IDE:

```sh
cargo creusot why3 ide verif/[COMA_FILE]
```

You must specify a Coma file, since there are lots of them in general.
