# Installation

This section explains how to install Creusot, what goes into the installation,
and some configuration options.

## Quick installation (using custom script)

The `INSTALL` script in the Creusot repository installs Creusot and its
accompanying tools.

Requirements to run the `INSTALL` script:

- `cargo`
- [`opam`](https://opam.ocaml.org/) to install `why3` and `why3find`.
- `curl` to download provers: `alt-ergo`, `z3`, `cvc4`, `cvc5`.

```sh
git clone https://github.com/creusot-rs/creusot
cd creusot
./INSTALL
```

See `./INSTALL --help` for options.

Note that the `INSTALL` script will take a couple minutes to create
a local Opam switch and then to install the many dependencies of `why3`.

The local switch will be located in `$XDG_DATA_HOME/creusot/_opam`
(default on Linux: `~/.local/share/creusot/_opam`). We recommend having this local
switch to prevent accidentally breaking your Creusot setup while working
on other OCaml projects.

## Quick installation (using `nix`)

If you are using `nix`, you do not need to have a copy of this repository.

We assume that you have nix installed on your system. Setup instructions can be found here: https://nixos.org/download

You can use nix shell to enter an interactive subshell containing the project:
```
nix shell "github:creusot-rs/creusot"
```
The project lives in this subshell and will disappear as soon as you leave the subshell.

If you do not have flakes enabled, you may get this error:
```
error: experimental Nix feature 'nix-command' is disabled; use ''--extra-experimental-features nix-command' to override
```

All you have to do is activate flakes temporarily by using `--extra-experimental-features 'nix-command flakes'`:
```
nix --extra-experimental-features 'nix-command flakes' shell "github:creusot-rs/creusot"
```

## Use Creusot within a project (using `nix`)

Here is a sample `flake.nix` that provides a shell with Creusot as a dependency, using `flake-parts`:
```
{{#include example-flake.nix}}
```

> [!WARNING]
>
> `rustup` might conflict with `mkCreusotWrapped`: make sure to not have `rustc` in your path if you encounter weird issues.


## Manual installation

Creusot stores its files in a data directory, which is:

- `$CREUSOT_DATA_HOME` if that environment variable is set;
- otherwise, on Linux, `$XDG_DATA_HOME/creusot`, which defaults to `~/.local/share/creusot`
  when `XDG_DATA_HOME` is unset;
- on macOS, a directory under `~/Library/Application Support/`.

On Linux, set `CREUSOT_DATA_HOME` before running the commands below:

```sh
export CREUSOT_DATA_HOME="${CREUSOT_DATA_HOME:-${XDG_DATA_HOME:-$HOME/.local/share}/creusot}"
```

To use a non-default location, set and export `CREUSOT_DATA_HOME` in your shell profile;
`cargo creusot` reads it at runtime.

1. You can install the core files from the Creusot repository with Cargo alone:

    ```sh
    # Install cargo-creusot
    cargo install --path cargo-creusot

    # Install creusot-rustc
    TOOLCHAIN=$(grep "nightly-[0-9-]*" --only-matching rust-toolchain)
    cargo install --path creusot-rustc --root $CREUSOT_DATA_HOME/toolchains/$TOOLCHAIN

    # Install the Creusot prelude
    cargo run --bin prelude-generator
    mkdir -p $CREUSOT_DATA_HOME/share/why3find
    cp -rT target/creusot/packages $CREUSOT_DATA_HOME/share/why3find/packages

    # Install config files
    cp why3find.json $CREUSOT_DATA_HOME/why3find.json
    cp creusot-install/creusot_why3.conf $CREUSOT_DATA_HOME/creusot_why3.conf
    ```

2. Install [`why3`](https://www.why3.org/) and [`why3find`](https://github.com/creusot-rs/why3find).
    Creusot requires the specific versions pinned in `creusot-deps.opam`,
    you can install them using a dedicated Opam switch:

    ```sh
    cp creusot-deps.opam $CREUSOT_DATA_HOME/
    opam switch create -y $CREUSOT_DATA_HOME
    mkdir -p $CREUSOT_DATA_HOME/bin
    ln -sf $CREUSOT_DATA_HOME/_opam/bin/why3 $CREUSOT_DATA_HOME/bin/why3
    ln -sf $CREUSOT_DATA_HOME/_opam/bin/why3find $CREUSOT_DATA_HOME/bin/why3find
    ```

3. The following provers must then be put in `$CREUSOT_DATA_HOME/bin`.
    The recommended versions are listed in
    `creusot-setup/src/tools_versions_urls.rs` (other versions may work but are not tested).
    Refer to their respective project pages for how to get them:

    - [`alt-ergo`](https://alt-ergo.ocamlpro.com/) (downloadable binaries, also on Opam)
    - [`z3`](https://github.com/Z3Prover/z3) (downloadable binaries, also on Opam)
    - [`cvc5`](https://cvc5.github.io/) (downloadable binaries)
    - [`cvc4`](https://cvc4.github.io/) (downloadable binaries)

## Installed files

Everything Creusot needs to run.

- `cargo-creusot` in `PATH`. This is the entry point of Creusot.

- `$XDG_DATA_HOME/creusot/` (default on Linux: `~/.local/share/creusot`, overridden by
    `$CREUSOT_DATA_HOME` if set), a directory containing:

    - `toolchains/$TOOLCHAIN/bin/creusot-rustc`, the Creusot compiler, where `$TOOLCHAIN`
        is the toolchain used to build Creusot (set by the file `rust-toolchain` in the Creusot repository).

    - `bin/` containing binaries.

        - `why3` and `why3find`
        - Provers: `alt-ergo`, `z3`, `cvc5`, `cvc4`

    - `why3find.json`, the config file for Why3find (which is copied into new Creusot projects with
        `cargo creusot new` or `cargo creusot init`).

    - `creusot_why3.conf`, the config file for Why3.

    - `share/why3find/packages/creusot/creusot/`: the Creusot prelude (a Coma library).

- Only if you are installing a `X.Y.Z-dev` version, some additional configuration is required:

    - `$HOME/.cargo/config.toml` containing a `[patch.crates-io]` section with a local path to `creusot-std`.

        ```toml
        [patch.crates-io]
        creusot-std = { path = "/YOUR/PATH/TO/creusot/creusot-std" }
        ```

      As a shortcut, you can run `cargo creusot config --update` to set up this configuration.

## Why3

The Why3 configuration consists of two parts:

- `$XDG_DATA_HOME/creusot/creusot_why3.conf` contains information about provers and also defines strategies for use in Why3 IDE.
- `$XDG_CONFIG_HOME/creusot/why3.conf` (default on Linux: `~/.config/creusot`) contains user-specific settings.
    This file is generated by `cargo creusot` if it does not already exist (to set `running_provers_max`).
    Notable options in this file:

    - The maximum number of parallel prover jobs (`running_provers_max = ...`).
    - `[ide]` options for Why3 IDE (can be modified in the menu `File > Preferences`).

## Why3find

`cargo creusot` invokes `why3find`, which looks for the file `why3find.json` in the current working directory or one of its parents.
At the moment we recommend not modifying `why3find.json`. Instead, you should rely on adapting your Rust code to make proofs more robust, for example by adding more assertions.
Please open an issue if this configuration does not work for you.

Nevertheless, you may like to experiment with some of these options:

- `"fast"` and `"time"`: timeout durations in seconds for provers.
- `"depth"`: proof search is pruned after this number of levels.
- `"tactics"`: list of tactics to apply during proof search.
  "Tactics" are [Why3 transformations](https://www.why3.org/doc/technical.html#transformations) that take no arguments.
  For example: `compute_in_goal` and `inline_goal` are tactics; `apply H`, `exists X` are not tactics.

See [the Why3find README](https://git.frama-c.com/pub/why3find#why3find) for more information.

## Creusot versions

If you are just getting started with Creusot, we recommend that you install Creusot
from the default `master` branch.
This is the "dev version" `X.Y.Z-dev` where `X.Y.Z` is the upcoming version number.
The main benefit is to allow you to get fixes quicker if you run into issues.
The drawback is that your projects must then depend on the dev version of
the `creusot-std` crate. In particular, you cannot get it from crates.io,
and you have to apply "patches" in the Cargo config. This is handled
automatically by the installation instructions above (using `nix` or the `INSTALL` script),
but if you are installing everything manually, or you want to double-check your installation,
if you have installed a `X.Y.Z-dev` version (`0.12.0-dev` or later),
make sure to have a file `~/.cargo/config.toml` containing the following:

```toml
[patch.crates-io]
creusot-std = { path = "/YOUR/PATH/TO/creusot/creusot-std" }
```

We make a new release of Creusot every month, providing a clearly defined version
for your projects to depend on (as opposed to having to remember a specific commit hash).
This also enables getting the `creusot-std` crate from crates.io.
