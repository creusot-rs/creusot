![](/static/marteau.jpg)

*Le marteau-pilon, forges et aciéries de Saint-Chamond, Joseph-Fortuné LAYRAUD, 1889*

# About

**Creusot** is a *deductive verifier* for Rust code. It verifies your code is safe from panics, overflows, and assertion failures. By adding annotations you can take it further and verify your code does the *correct* thing.

Creusot works by translating Rust code to WhyML, the verification and specification language of [Why3](https://why3.lri.fr). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

See [ARCHITECTURE.md](ARCHITECTURE.md) for technical details.

## Help and Discussions

If you need help using Creusot or would like to discuss, you can post on the [discussions forum](https://github.com/creusot-rs/creusot/discussions) or join our [Zulip chat](https://why3.zulipchat.com/#narrow/stream/341707-creusot)!

## Citing Creusot

If you would like to cite Creusot in academic contexts, we encourage you to use our [ICFEM'22 publication](https://hal.inria.fr/hal-03737878/file/main.pdf).

# Examples of Verification

To get an idea of what verifying a program with Creusot looks like, we encourage you to take a look at some of our test suite:

- [Zeroing out a vector](creusot/tests/should_succeed/vector/01.rs)
- [Binary search on Vectors](creusot/tests/should_succeed/vector/04_binary_search.rs)
- [Sorting a vector](creusot/tests/should_succeed/vector/02_gnome.rs)
- [IterMut](creusot/tests/should_succeed/iterators/02_iter_mut.rs)
- [Normalizing If-Then-Else Expressions](creusot/tests/should_succeed/ite_normalize.rs)

More examples are found in [creusot/tests/should_succeed](creusot/tests/should_succeed).

## Projects built with Creusot

- [CreuSAT](https://github.com/sarsko/creusat) is a verified SAT solver written in Rust and verified with Creusot. It really pushes the tool to its limits and gives an idea of what 'use in anger' looks like.
- Another big project is in the works :)

# Installing Creusot as a user

1. [Install `rustup`](https://www.rust-lang.org/tools/install), to get the suitable Rust toolchain
2. [Get `opam`](https://opam.ocaml.org/doc/Install.html), the package manager for OCaml
3. Clone the [creusot](https://github.com/creusot-rs/creusot/) repository,
   then *move into the `creusot` directory* for the rest of the setup.
    ```
    $ git clone https://github.com/creusot-rs/creusot
    $ cd creusot
    ```
4. Set up **Why3** and **Alt-Ergo**. Create a local `opam` switch with why3 and alt-ergo:
   ```
   $ opam switch create -y . ocaml.4.14.1
   $ eval $(opam env)
   ```
   This will build why3, alt-ergo and their ocaml dependencies in a local `_opam` directory.
5. Build **Creusot**:
    ```
    $ cargo install --path creusot-rustc
    $ cargo install --path cargo-creusot
    ```
    this will build the `cargo-creusot` and `creusot-rustc` executables and place them in `~/.cargo/bin`.
6. Set up **Creusot**:
   ```
   $ cargo creusot setup install
   ```
   this will download additional solvers (Z3, CVC4, CVC5) and configure Why3 to use them.

# Upgrading Creusot 

1. Enter the cloned Creusot git repository used previously to install Creusot
2. Update Creusot's sources:
   ```
   $ git pull
   ```
2. Upgrade Why3 and Alt-Ergo if needed:
   ```
   $ eval $(opam env)
   $ opam update
   $ opam install .
   ```
3. Rebuild and reinstall Creusot:
   ```
   $ cargo install --path creusot-rustc
   $ cargo install --path cargo-creusot
   ```
4. Re-run Creusot's setup:
   ```
   $ cargo creusot setup install
   ```

# Verifying with Creusot and Why3

See the [guide](https://creusot-rs.github.io/creusot/).


# Hacking on Creusot

See [HACKING.md](HACKING.md) for information on the developer workflow for
hacking on the Creusot codebase.
