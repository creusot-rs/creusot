We thank you, contributor, for working to improve the Creusot tool for Rust verification.

# 0. Legal Front matter

In order to be able to merge contributions to the source code of Creusot, authors of non-trivial contributions need to agree with the Contributor License Agreement (CLA) given in the entity-CLA.pdf individual-CLA.pdf files, depending on your status. If you want to write such a contribution, please print, sign and send the relevent form to the development team, both in digital and printed versions.

# 1. Installing a development environment

Follow the instructions provided in the [README](./README.md). This will provide a working development for Creusot and proofs.

# 2. Running tests

## 2.1. UI Tests

The UI tests are used to validate the translation of Creusot. They can be found in `creusot/tests/should_fail` and `creusot/tests/should_suceed`.
Ideally, each test includes a comment specifying the property or feature being checked.
To validate the translation one can run `cargo test --test ui`, or to run only a subset of tests run `cargo test --test ui -- "string-pattern"`.

## 2.2. Updating UI tests

If you have made changes to the Creusot translation and the UI tests show a diff you believe to be legitimate, you can tell Creusot to record the new output using `cargo test --test ui -- "pattern" --bless`.
When contributing or updating tests, we ask that you minimize avoidable warnings, in particular, top-level declarations should be marked public, and unused arguments removed or replaced by wildcards.
The warnings and errors of each test are recorded in an accompanying `stderr` file if any were present.

# 4. Verifying proofs

Once you are satisfied with the MLCFG output, you can validate the proofs of Creusot by running `cargo test --test why3`. This will run each test in the UI suite, and if a Why3 session is found, execute the proofs within.
If you add a test that you believe should include a proof, you can add it using the `./ide` script provided in Creusot.
Load your test case in the Why3 IDE, solve the proof and save the result, it will now be checked as part of CI.

Because verifying the proofs can be tedious during development the `cargo test --test why3` command accepts two flags: `--diff-from=` which accepts a Git ref and only checks the MLCFG files that have changed since then, and `--replay=` which accepts one of three values: `none`, `obsolete`, `all` and guides which proofs should actually be run or only just typecheked.

Helpful cheatsheet:
- `cargo test --test why3 -- --diff-from=master --replay=none`: only typecheck the test cases that have changed
- `cargo test --test why3 -- --diff-from=master --replay=obsolete`: run the proofs for all changed test cases, which in normal circumstances should be the only ones that matter

