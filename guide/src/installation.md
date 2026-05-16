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
{
  inputs = {
    # Both `nixpkgs` and `flake-parts` are pinned to the same version as Creusot's
    nixpkgs.follows = "creusot/nixpkgs";
    flake-parts.follows = "creusot/flake-parts";

    creusot.url = "github:creusot-rs/creusot";
  };

  outputs =
    inputs@{
      creusot,
      flake-parts,
      nixpkgs,
      self,
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "x86_64-linux"
      ];

      perSystem =
        {
          pkgs,
          system,
          ...
        }:
        {
          # `pkgs` will also contain the `creusot` set, thanks to Creusot's overlay
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ creusot.overlays.default ];
          };

          # `nix fmt`
          formatter = pkgs.nixfmt-tree;

          # `nix develop`
          devShells.default = pkgs.mkShell {
            packages = [
              # `mkCreusotWrapped` produces a wrapped version of Creusot, along with all its dependencies (similar to `clang`).
              # The `isFree` argument allows switching between the free and non-free version of the solver `alt-ergo`.
              (pkgs.creusot.mkCreusotWrapped { isFree = true; })

              # Further packages could be added, notably `cargo` for the `cargo creusot` command
              pkgs.cargo
              pkgs.clippy
              pkgs.rust-analyzer
              pkgs.rustfmt
              # ...
            ];
          };
        };
    };
}
```

## Manual installation

1. You can install the core files from the Creusot repository with Cargo alone:

    ```sh
    # Install cargo-creusot
    cargo install --path cargo-creusot

    # Install creusot-rustc
    TOOLCHAIN=$(grep "nightly-[0-9-]*" --only-matching rust-toolchain)
    cargo install --path cargo-creusot --root $XDG_DATA_HOME/creusot/toolchain/$TOOLCHAIN/bin

    # Install the Creusot prelude
    cargo run --bin prelude-generator
    mkdir -p $XDG_DATA_HOME/share/why3find
    cp -rT target/creusot/packages $XDG_DATA_HOME/share/why3find/packages

    # Copy why3find.json in the installation directory
    cp cargo-install/why3find.json $XDG_DATA_HOME/creusot/why3find.json
    ```

2. The following binaries must then be put in `$XDG_DATA_HOME/creusot/bin`, refer to their respective
    project pages for how to get them:

    - [`why3`](https://www.why3.org/) (available on Opam)
    - [`why3find`](https://git.frama-c.com/pub/why3find) (available on Opam)
    - [`alt-ergo`](https://alt-ergo.ocamlpro.com/) (downloadable binaries, also on Opam)
    - [`z3`](https://github.com/Z3Prover/z3) (downloadable binaries, also on Opam)
    - [`cvc5`](https://cvc5.github.io/) (downloadable binaries)
    - [`cvc4`](https://cvc4.github.io/) (downloadable binaries)

## Installed files

Everything Creusot needs to run.

- `cargo-creusot` in `PATH`. This is the entry point of Creusot.

- `$XDG_DATA_HOME/creusot/` (default on Linux: `~/.local/share/creusot`), a directory containing:

    - `toolchain/$TOOLCHAIN/bin/creusot-rustc`, the Creusot compiler, where `$TOOLCHAIN`
        is the toolchain used to build Creusot (set by the file `rust-toolchain` in the Creusot repository).

    - `bin/` containing binaries.

        - `why3` and `why3find`
        - Provers: `alt-ergo`, `z3`, `cvc5`, `cvc4`

    - `why3find.json`, which is used to create new Creusot projects with
        `cargo creusot new` or `cargo creusot init`.

    - `share/why3find/packages/creusot/creusot/`: the Creusot prelude (a Coma library).

## Why3

The Why3 configuration is located at `$XDG_CONFIG_HOME/creusot/why3.conf`
(default on Linux: `~/.config/creusot`). This file is generated by `cargo creusot`
if it does not already exist, and by `cargo creusot why3-conf`. Notable options in this file:

- the location and version of provers (`[partial_prover]`)
  (for the Nix installation, this is not known during the installation of Creusot,
  that's why this file is generated later).
- The maximum number of parallel prover jobs (`running_provers_max = ...`).
- `[strategy]` for solving goals in Why3 IDE.
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
and you have to apply "patches" in the Cargo config.
`cargo creusot new` handles this automatically in simple cases,
but some intervention may be necessary when switching between a dev version
and a released version of Creusot.

We make a new release of Creusot every month, providing a clearly defined version
for your projects to depend on (as opposed to having to remember a specific commit hash).
This also enables getting the `creusot-std` crate from crates.io.
