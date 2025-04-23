# Command-line Interface

## List of commands

- [`cargo creusot`](#creusot)
- [`cargo creusot prove`](#prove)
- [`cargo creusot doc`](#doc)
- [`cargo creusot clean`](#clean)
- [`cargo creusot new`](#new)
- [`cargo creusot init`](#init)
- [`cargo creusot setup status`](#setup-status)

## Main commands

### `creusot`

```
cargo creusot [-- [-p <CRATE>]]
```

Run the Creusot compiler.

Output Coma code in the `verif/` directory.

#### Options

- `-p <CRATE>`: Compile a specific crate `<CRATE>` in a multi-crate project.

### `prove`

```
cargo creusot prove [-i] [<COMA_FILE>]
```

Verify contracts.

This first runs `cargo creusot` to be sure that the compiled code is up-to-date.
Then `why3find` verifies the compiled Coma code: it generates verification conditions
and tries to prove them.

#### Options

- `-i`: Open the Why3 IDE on an unproved file to inspect its proof context.
- `<COMA_FILE>`: Verify a specific file (corresponding to one Rust function).

### `doc`

```
cargo creusot doc
```

Build documentation.

This is a variant of `cargo doc` that also renders contracts (`requires` and `ensures`), logic functions, and predicates.


### `clean`

```
cargo creusot clean [--force] [--dry-run]
```

Remove dangling proof files.

Removing (or renaming) Rust functions also removes (or renames) its compiled Coma file.
However, the Creusot compiler can't keep track of their associated proof files (`proof.json`, `why3session.xml`), which become dangling.
`cargo creusot` will detect dangling files and print a warning to remind you to move those files if you want,
otherwise you can remove them with `cargo creusot clean`.

#### Options

- `--force`: Don't ask for confirmation before removing dangling files.
- `--dry-run`: Only print the list of files that would be removed by `cargo creusot clean`.

## Create and maintain package

### `new`

```
cargo creusot new <NAME> [--main]
```

Create or update package named `<NAME>`.

Create directory `<NAME>` if it doesn't already exist, and run `cargo creusot init` inside it.

#### Options

- `--main`: Create `main.rs` for an executable crate. (By default, only a library crate `lib.rs` is created.)

### `init`

```
cargo creusot init [<NAME>] [--main]
```

Create or update package in the current directory.

If `Cargo.toml` doesn't exist, create a new package with starting configuration and source files.

If `Cargo.toml` exists, update an existing package for verification with Creusot:

- add or update `creusot-contracts` in the list of dependencies with the version matching your Creusot installation;

    For released versions of Creusot, this is equivalent to `cargo add creusot-contracts@<VERSION>` just with the right version.

    For a development version of Creusot (prerelease version `-dev`), this also adds the following lines:

    ```
    [patch.crates-io]
    creusot-contracts = { path = "/path/to/creusot-contracts" }
    ```

    This setting is documented in [The Cargo Book: Overriding Dependencies](https://doc.rust-lang.org/cargo/reference/overriding-dependencies.html).

- add `why3find.json` if it doesn't exist.

#### Options

- `<NAME>`: Name of the package. (By default, it is the name of the directory.)
- `--main`: Create `main.rs` for an executable crate. (By default, only a library crate `lib.rs` is created.)

## Show configuration

### `setup status`

```
cargo creusot setup status
```

Show the status of the Creusot installation.

Print tool locations and configuration paths.