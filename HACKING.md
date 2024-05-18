# Hacking on Creusot: developer workflow

This is a work-in-progress document describing the developer workflow for
working on the Creusot codebase.

## Setup

The testsuite will use the global Creusot configuration managed by 
`cargo creusot setup`. 
You first need to have successfully run `cargo creusot setup install` as
detailed in the README installation instructions.

**To be able to use custom versions of Why3 or the solvers** (instead of the
built-in ones expected by Creusot), one can pass extra flags to 
`cargo creusot setup install` (see also `--help`):
- `--external <TOOL>` to specify that a solver should be looked up from the path
- `--no-check-version <TOOL>` to allow unexpected versions of a given tool

To avoid first installing the `cargo-creusot` binary before running `cargo
  creusot setup`, one can directly call it from the git repository: `cargo run
  --bin cargo-creusot creusot setup`

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
