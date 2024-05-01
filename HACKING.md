# Hacking on Creusot: developer workflow

This is a work-in-progress document describing the developer workflow for
working on the Creusot codebase.

## Setup

The "Creusot developer setup" sometimes requires more flexibility in how it
looks up why3 and related solvers, compared to the standard "user" workflow
provided by `cargo creusot setup install`. You have two options:

- **By default** the testsuite will use the global Creusot configuration managed
  by `cargo creusot setup`. You first need to have successfully run `cargo
  creusot setup install` (or `cargo creusot setup install-external`).
- **Alternatively** you can set a custom "developer" Creusot configuration in
  `.creusot-config/` at the root of the git repo. Start by running `cp -r
  .creusot-config.sample .creusot-config`. This will tell the testsuite to use
  whichever `why3` binary is in the PATH, but you can also tweak
  `.creusot-config/Config.toml` to point to a specific binary.

The first option is recommended if you simply want a working setup to run the
testsuite.

The second option is useful if you need to try custom versions of Why3 or the
solvers.

Notes:
- to avoid first installing the `cargo-creusot` binary before running `cargo
  creusot setup`, one can directly call it from the git repository: `cargo run
  --bin cargo-creusot creusot setup`
- the format of the `.creusot-config/` directory is simply the same as
  `~/.config/creusot`, which is where `cargo creusot setup` writes its
  configuration.

## Running the testsuite

- Test the output of creusot (mlcfg files) against reference files:
```
cargo test --test ui
```

Then, to update an out-of-date reference file:
```
cargo test --test ui -- "optional-string" --bless
```

(NB: to bless all the tests, you need to pass the empty string `""`)

- Replay proofs:
```
cargo test --test why3
```

Additional useful parameters, to avoid replaying *every* proof in development:
- `--diff-from=GIT_REF`
- `--replay=<none|obsolete|all>`

## Inspecting/fixing the proof of a test

If the proof of a test is broken (e.g.
`creusot/tests/should_succeed/cell/01.rs`), launch the why3 ide with `./ide`:
```
./ide creusot/tests/should_succeed/cell/01
```

## Calling why3 & why3_tools: shell environment setup

To invoke why3 (manually or in scripts) with the same binary/configuration as
setup by `cargo creusot setup`, one needs to setup a shell environment with the
correct PATH and environment variables.

To do so, we provide the following command:
```
eval $(cargo run --bin dev-env)
```

After that, the `why3` binary in PATH will be the one configured by
`cargo creusot setup`, using the adequate configuration file (through the
`WHY3CONFIG` environment variable).

## Upgrading the revision of Why3 used by Creusot

Edit `creusot-deps.opam` to use the hash of the git commit of the latest commit
in Why3's master branch. (But first make sure that the Nightly CI job passes.)

There are several places to edit in the file: the `pin-depends` field at the end
of the file (URLs and `git-XXXX` versions), and the `git-XXXX` versions in the
`depends:` field.
