We thank you, contributor, for working to improve the Creusot tool for Rust verification.

# 1. Installing a development environment

Follow the instructions provided in the [README](./README.md). This will provide a working development for Creusot and proofs.

# 2. Running tests

## 2.1. UI Tests

The UI tests are used to validate the translation of Creusot. They can be found in `tests/should_fail` and `tests/should_suceed`.
Ideally, each test includes a comment specifying the property or feature being checked.
To validate the translation one can run `cargo test --test ui`, or to run only a subset of tests run `cargo test --test ui "pattern"`.

## 2.2. Updating UI tests

If you have made changes to the Creusot translation and the UI tests show a diff you believe to be legitimate, you can tell Creusot to record the new output using `cargo test --test ui "pattern" -- --bless`.
When contributing or updating tests, we ask that you minimize avoidable warnings, in particular, top-level declarations should be marked public, and unused arguments removed or replaced by wildcards.
The warnings and errors of each test are recorded in an accompanying `stderr` file if any were present.

The `ui` test also runs the Creusot translation on `creusot-contracts`.
The result is located at `tests/creusot-contracts/creusot-contracts.coma`.
To run the translation only on `creusot-contracts`, use a pattern that matches nothing, like `cargo test --test ui qq`

# 3. Verifying proofs

Once you are satisfied with the coma output, you can validate the proofs of Creusot by running `cargo test --test why3`. This will run each test in the UI suite, and if a Why3 session is found, execute the proofs within.
If you add a test that you believe should include a proof, you can add it using the `./ide` script provided in Creusot.
Load your test case in the Why3 IDE, solve the proof and save the result, it will now be checked as part of CI.

Options:

- `--update`: update `proof.json` files (for `why3find` tests). (`why3session.xml` files
    for `why3` tests with obsolete goals are automatically updated.)

- `--diff-from=` (accepts a Git ref): only check the coma files that have changed since then.
