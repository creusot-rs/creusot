We thank you, contributor, for working to improve the Creusot tool for Rust verification.

# 1. Install Creusot

Follow the instructions provided in the [README](./README.md). This will provide a working development for Creusot and proofs.

# 2. Running tests

Run the default tests:

```sh
./t
```

For additional options, see `./t all`

## 2.1. UI Tests

The UI tests are used to validate the translation of Creusot. They can be found in `tests/should_fail` and `tests/should_suceed`.
Ideally, each test includes a comment specifying the property or feature being checked.
To validate the translation one can run `./t ui` (long form: `cargo test --test ui`), or to run only a subset of tests run `./t ui "pattern"` (long form: `cargo test --test ui -- "pattern"`).

## 2.2. Updating UI tests

If you have made changes to the Creusot translation and the UI tests show a diff you believe to be legitimate, you can tell Creusot to record the new output using  `./t ui --update`.
When contributing or updating tests, we ask that you minimize avoidable warnings, in particular, top-level declarations should be marked public, and unused arguments removed or replaced by wildcards.
The warnings and errors of each test are recorded in an accompanying `stderr` file if any were present.

The `ui` test also runs the Creusot translation on `creusot-std`.
The result is located at `tests/creusot-std/creusot-std.coma`.

# 3. Verifying proofs

Once you are satisfied with the coma output, you can validate the proofs of Creusot by running `./t why3` (long form: `cargo test --test why3`). This will run each test that has changes compared to the branch `origin/master`, and if a Why3 session is found, execute the proofs within.

Options for `./t why3`:

- `--update`: update `proof.json` files (for `why3find` tests). (Tests with `why3session.xml`
    files are automatically updated if they have "obsolete" goals (minor changes);
    for more substantial changes, you must edit them with `./ide MY/TEST/NAME/why3session.xml`.)

- `--why3-all`: update all tests (default is only those with changes from `origin/master`)

Note: the `why3` tests currently requires an installation of the supporting tools Why3, Why3find, and provers.
The simplest way to get them in the right locations is to run the installer `./INSTALL`;
some steps can be skipped with `./INSTALL --skip-creusot-rustc --skip-cargo-creusot` if you only care about running the test suite.

## Inspecting/fixing the proof of a test

If the proof of a test is broken (e.g.
`tests/should_succeed/cell/01.rs`), launch the why3 ide with `./ide`:
```
./ide tests/should_succeed/cell/01
```

# More hacking tips

This is a work-in-progress document describing the developer workflow for
working on the Creusot codebase.

## Setup

The testsuite will use the global Creusot configuration managed by
`cargo creusot setup`.
You first need to have successfully run `./INSTALL` as
detailed in the README installation instructions.

**To be able to use custom versions of Why3 or the solvers** (instead of the
built-in ones expected by Creusot), one can pass extra flags to
`./INSTALL` (see also `--help`):
- `--external <TOOL>` to specify that a solver should be looked up from the path
- `--no-check-version <TOOL>` to allow unexpected versions of a given tool

## Calling why3 (and why3_tools, etc): shell environment setup

To invoke why3 (manually or in scripts) with the same binary/configuration as
setup by `./INSTALL`, one needs to setup a shell environment with the
correct PATH and environment variables.

To do so, we provide the following command:
```
eval $(cargo run --bin dev-env)
```

After that, the `why3` binary in PATH will be the one configured by
`./INSTALL`, using the adequate configuration file (through the
`WHY3CONFIG` environment variable).

## Upgrading Why3

Edit `creusot-deps.opam` to use the hash of the git commit of the latest commit
in Why3's master branch. (But first make sure that the Nightly CI job passes.)

There are several places to edit in the file: the `pin-depends` field at the end
of the file (URLs and `git-XXXX` versions), and the `git-XXXX` versions in the
`depends:` field.

## Upgrading a prover to a newer version

- Install why3-tools: `opam pin git+https://github.com/xldenis/why3-tools`
- Install the newer prover, make it available in `$PATH`
- Setup Creusot to use it: `./INSTALL --no-check-version <PROVER> --external <PROVER>`
- Run `eval $(cargo run --bin dev-env)`
- Use the `./testsuite_upgrade_prover` script to update why3 sessions in the testsuite.
  Launch the script without arguments to have some usage instructions.
  To instead regenerate a session from scratch, use the `./testsuite_regenerate` script.
- Once the testsuite is migrated, update `creusot-setup/src/{tools,tools_versions_urls}.rs`
