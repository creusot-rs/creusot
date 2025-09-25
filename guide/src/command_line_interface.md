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
cargo creusot [--erasure-check] [-- [-p <CRATE>]]
```

Run the Creusot compiler.

Output Coma code in the `verif/` directory.

#### Creusot options

- `--erasure-check`: Report `#[erasure]` check failures as errors; see [Erasure check](erasure.html).

    + `--erasure-check=no`: Disable `#[erasure]` checks.
    + `--erasure-check=warn` (default): Report `#[erasure]` check failures as warnings.

#### Cargo options

All options after `--` are forwarded to `cargo`. Here is a selection of useful ones for Creusot users:

- `-p <CRATE>`: Compile a specific crate `<CRATE>` in a multi-crate project.
- `-Zbuild-std`: Recompile crates `core`, `std`, `alloc`, `proc-macro`. (Useful for `--erasure-check`.)

### `prove`

```
cargo creusot prove [<PATTERNS>] [-i|--ide-on-fail|--ide-always] [--replay] [--why3session]
```

Verify contracts.

This first runs `cargo creusot` to be sure that the compiled code is up-to-date.
Then `why3find` verifies the compiled Coma code: it generates verification conditions
and tries to prove them.

#### Options

- `<PATTERNS>`: Select Coma files that match one of the patterns.
  If no patterns are provided, prove all files.
  Example patterns: `name`, `name::*`, `m/*/f`. Separators can be written as `::` or `/`.
- `-i`, `--ide-on-fail`: Open the Why3 IDE on an unproved file to inspect its proof context.
- `--ide-always`: Open the Why3 IDE on a single Coma file regardless of whether the proof succeeded.
  The command fails if `<PATTERN>` does not match exactly one file.
- `--replay`: Don't generate new proofs, only check if the existing proofs are valid.
- `--why3session`: Generate `why3session.xml` files (implied by `-i` and `--ide-always`).

### `doc`

```
cargo creusot doc
```

Build documentation.

This is a variant of `cargo doc` that also renders contracts (`requires` and `ensures`) and logic functions.


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

### `why3 ide`

```
cargo creusot why3 ide <COMA_FILE|why3session.xml>
```

Run the Why3 IDE on a Coma file or a `why3session.xml`.
This commands simply invokes `why3 ide` with the
required options to load Coma files produced by Creusot.

This is a command for experts and for troubleshooting.
In normal usage, prefer `cargo creusot prove` with `-i` or `--ide-always`,
which ensures that the Coma artifacts are always up to date.

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
