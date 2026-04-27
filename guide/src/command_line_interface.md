# Command-line Interface

## List of commands

- [`cargo creusot`](#creusot)
- [`cargo creusot doc`](#doc)
- [`cargo creusot clean`](#clean)
- [`cargo creusot why3 ide`](#why3-ide)
- [`cargo creusot new`](#new)
- [`cargo creusot init`](#init)
- [`cargo creusot why3-conf`](#why3-conf)
- [`cargo creusot version`](#version)

## Main commands

### `creusot`

```
cargo creusot
  [-p <PACKAGE>] [--only=(coma|prove)]
  [--erasure-check]
  <PATTERN>* [-i|--ide-on-fail|--ide-always]
  [--replay] [--why3session] [--why3find-arg <ARG>] [--dry-run-why3find]
  [-- <CARGO_OPTIONS>]
```

Run Creusot: compile to Coma (into the `verif/` directory)
and run provers on verification conditions (using Why3find).

#### Creusot options

- `-p <PACKAGE>`: Only build `<PACKAGE>` (in multi-package workspaces).
    By default, all *default members* of a workspace are built, determined by one of the
    following configurations, in decreasing order of priority:

    + the `default-members` field of `[workspace.metadata.creusot]` in `Cargo.toml`

        ```toml
        [workspace.metadata.creusot]
        default-members = ["package1", "package2"]
        ```

    + [the `default-members` field][cargo-default-members] of `[workspace]` in `Cargo.toml`

        ```toml
        [workspace]
        default-members = ["package1", "package2"]
        ```

    + if neither of these fields exists, then the default members are---as
      defined by [Cargo][cargo-default-members]---either just the root package,
      if it exists, or all members of the workspace.

    Within a package, Creusot only compiles **libraries and binaries**.
    Tests, examples, and benches are currently unsupported.
    (Please reach out if you need this feature!)

- `--erasure-check`: Report `#[erasure]` check failures as errors; see [Erasure check](erasure.html).

    + `--erasure-check=no`: Disable `#[erasure]` checks.
    + `--erasure-check=warn` (default): Report `#[erasure]` check failures as warnings.

- `--only=coma`: Only typecheck and compile to Coma, no provers.
- `--only=prove`: Only run provers without compiling to Coma (your Coma files may be out of date!).

#### Prover-specific options

- `<PATTERN>`: Select Coma files that match one of the patterns.
  If no patterns are provided, prove all files in selected packages (`-p`).
  Example patterns: `name`, `name::*`, `m/*/f`. Separators can be written as `::` or `/`.
- `-i`, `--ide-on-fail`: Open the Why3 IDE on an unproved file to inspect its proof context.
- `--ide-always`: Open the Why3 IDE on a single Coma file regardless of whether the proof succeeded.
  The command fails if `<PATTERN>` does not match exactly one file.
- `--replay`: Don't generate new proofs, only check if the existing proofs are valid.
- `--why3session`: Generate `why3session.xml` files (implied by `-i` and `--ide-always`).
- `--why3find-arg <ARG>`: pass `<ARG>` directly as an extra argument to `why3find prove`. Repeat this to pass multiple arguments.
- `--dry-run-why3find`: Print the `why3find` command without running it.

[cargo-default-members]: https://doc.rust-lang.org/cargo/reference/workspaces.html#the-default-members-field

#### Cargo options

All options after `--` are forwarded to `cargo`. Here is a selection of useful ones for Creusot users:

- `-Zbuild-std`: Recompile crates `core`, `std`, `alloc`, `proc-macro`. (Useful for `--erasure-check`.)

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
In normal usage, prefer `cargo creusot` with `-i` or `--ide-always`,
which ensures that the Coma artifacts are always up to date.

## Create and maintain package

### `new`

```
cargo creusot new <NAME> [--main] [--creusot-std <PATH>]
```

Create or update package named `<NAME>`.

Create directory `<NAME>` if it doesn't already exist, and run `cargo creusot init` inside it.

#### Options

- `--main`: Create `main.rs` for an executable crate. (By default, only a library crate `lib.rs` is created.)
- `--creusot-std <PATH>`: Path to local `creusot-std` used to set the `[patch.crates-io]` section of `Cargo.toml`.

### `init`

```
cargo creusot init [<NAME>] [--main]
```

Create or update package in the current directory.

If `Cargo.toml` doesn't exist, create a new package with starting configuration and source files.

If `Cargo.toml` exists, update an existing package for verification with Creusot:

- add or update `creusot-std` in the list of dependencies with the version matching your Creusot installation;

    For released versions of Creusot, this is equivalent to `cargo add creusot-std@<VERSION>` just with the right version.

    For a development version of Creusot (prerelease version `-dev`), this also adds the following lines:

    ```
    [patch.crates-io]
    creusot-std = { path = "/path/to/creusot-std" }
    ```

    This setting is documented in [The Cargo Book: Overriding Dependencies](https://doc.rust-lang.org/cargo/reference/overriding-dependencies.html).

- add `why3find.json` if it doesn't exist.

#### Options

- `<NAME>`: Name of the package. (By default, it is the name of the directory.)
- `--main`: Create `main.rs` for an executable crate. (By default, only a library crate `lib.rs` is created.)
- `--creusot-std <PATH>`: Path to local `creusot-std` used to set the `[patch.crates-io]` section of `Cargo.toml`.

## Configuration

### `why3-conf`

```
cargo creusot why3-conf [--provers-parallelism <N>]
```

Regenerate `why3.conf` (in `$XDG_CONFIG_HOME/creusot/`, by default on Linux `.config/creusot/`).

#### Options

- `--provers-parallelism`: Set the max number of threads to use to invoke SMT provers.
    (Default: automatically detect the number of threads for your machine)

### `version`

```
cargo creusot version
```

Print version of Creusot and accompanying tools.
