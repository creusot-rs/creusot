# Hacking on Creusot: developer workflow

This is a work-in-progress document describing the developer workflow for
working on the Creusot codebase.

## Setup

On top of the usual Rust/Cargo workflow, the "Creusot developer setup" requires
a working Why3 in order to run the testsuite and update tests proofs. You have
two choices:

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

## Calling why3

To invoke why3 robustly (manually or in scripts), we provide a wrapper that will
lookup the why3 path and config according to the logic described in **Setup**
above.

To invoke why3 this way, run:
```
cargo run --bin dev-why3 -- <arguments_to_why3...>
```
