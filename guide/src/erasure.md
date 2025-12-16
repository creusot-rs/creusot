# Erasure check

Verifying functions with Creusot requires modifying their code to add attributes, assertions, ghost code, *etc.*.
This creates a gap between the function that is verified and the function that is compiled and run.
The disconnect is two-fold:

1. The verified function is different from the original function.
   One may still want to keep using the original function for various reasons,
   including avoiding a dependency on Creusot.
2. Even if you compile the verified function, that relies on erasing Creusot annotations,
   which may affect trait resolution and result in compiling a different function
   than the one that was verified by Creusot.

To bridge that gap, the `#[erasure(...)]` attribute maintains a tight connection
between the verified function and the original function.

## Overview

The attribute `#[erasure(f)]` is put on a function definition.
It asserts that the annotated function `f2` (to be verified by Creusot) and the target `f`
(to be compiled) have the same runtime behavior.
This is a syntactic check that tries to simply match the bodies of `f` and `f2` with each other
modulo small code transformations to ignore purely logical constructs.

```rust
#[erasure(f)]
fn f2(x: A) {
    /* ... */
}
```

The `#[erasure]` check performs the following operations.

- Erase `Ghost` and `Snapshot` variables, `ghost!`, `snapshot!`, and `proof_assert!` blocks,
  `#[ensures]`, `#[requires]`, `#[invariant]` attributes.
- Replace called functions with their own `#[erasure]`.
- Equate up to A-normal form.

`#[trusted]` functions skip the `#[erasure]` check.

Additional rules for pointers:

- [`Perm::as_ref(ptr)`](https://creusot-rs.github.io/creusot/doc/creusot_contracts/ghost/struct.Perm.html#method.as_ref) erases to `&*ptr` (pointer-to-reference coercion).
- [`Perm::as_mut(ptr)`](https://creusot-rs.github.io/creusot/doc/creusot_contracts/ghost/struct.Perm.html#method.as_mut) erases to `&mut *ptr` (pointer-to-reference coercion).
- [`Perm::from_ref(r)`](https://creusot-rs.github.io/creusot/doc/creusot_contracts/ghost/struct.Perm.html#method.from_ref) erases to `r as *const T` (reference-to-pointer coercion).
- [`Perm::from_mut(r)`](https://creusot-rs.github.io/creusot/doc/creusot_contracts/ghost/struct.Perm.html#method.from_mut) erases to `r as *mut T` (reference-to-pointer coercion).

## Example

Consider the following generic example of "unverified code".
The function `h` calls two functions `f` and `g`:

```rust
fn h(x: A) {
    g(f(x))
}

fn f(x: A) -> B { /* ... */ }
fn g(y: B) { /* ... */ }
```

"Verifying" these functions with Creusot may involve introducing ghost arguments,
ghost blocks, assertions, *etc.*, resulting in code that looks as follows.

```rust
#[erasure(h)]
#[requires(...)]
#[ensures(...)]
fn h2(x: A) {
    let (y, i) = f2(x);
    ghost!(...);
    g2(y, i)
}

#[erasure(f)]
fn f2(x: A) -> (B, Ghost<I>) { /* ... */ }

#[erasure(g)]
fn g2(y: B, i: Ghost<I>) { /* ... */ }
```

The attribute `#[erasure(h)]` checks that `h2` behaves the same as the previous `h` if we ignore ghost code.
In order to do this check, Creusot performs a couple of transformations to the body of `h`.

First, erase ghost blocks, ghost variables, and assertions:

```rust
fn h2(x: A) {
    let (y, _) = f2(x);
    g2(y, _)
}
```

Replace `f2` with its erasure `f`, `g2` with its erasure `g` (as indicated by their own `#[erasure]` attributes).
The erasure of `f2` also replaces its result tuple with its only non-ghost component.

```rust
fn h2(x: A) {
    let y = f(x);
    g(y)
}
```

Before comparing `h2` and `h`, we put them both in A-normal form. Here, `h2` is simple and already in A-normal form.
The body `f(g(x))` of the function `h` gets rewritten as follows.

```rust
fn h(x: A) {
    let y = f(x);
    g(y)
}
```

Now `h2` and `h` are identical, so the `#[erasure(h)]` check succeeds.

## Usage

### Intra-crate checks

When `#[erasure(f)]` mentions a function `f` defined in the same crate
as the annotated function, the erasure check works simply as you would expect.

### Cross-crate checks

When `#[erasure(f)]` mentions a function `f` from another crate,
`#[erasure]` check failures are reported as warnings by default
because they require some setup to work.

The `#[erasure]` check requires compiling your whole project twice: the first time to know what definitions
need to be checked, and the second time to get dependencies to export those definitions. The reason is that
`#[erasure]` compares THIR ASTs, which exist only during the compilation of the crate containing those definitions.

The required definitions are stored as binary blobs in the folder `_creusot_erasure` so that they persist
when removing `target/creusot` to force a rebuild.

```
cargo creusot
rm -r target/creusot # Force rebuilding from scratch
cargo creusot --erasure-check
```

To keep the metadata for `#[erasure]` checks up to date, you must recompile twice whenever you add new
`#[erasure]` annotations or you update a dependency.

Due to this, `#[erasure]` checks give different errors depending on whether you have rebuilt your
project from scratch at least once ("missing bodies" vs. "the actual check failed").
For that reason, these failures are reported as warnings by default.
Use the option `--erasure-check` to report them as errors instead.

The variants of this option are:

- `--erasure-check=no`: disable `#[erasure]` checks;
- `--erasure-check=warn` (default): report `#[erasure]` check failures as warnings;
- `--erasure-check` (or `--erasure-check=error`): report `#[erasure]` check failures as errors.

### Using `core` and `std`

When `#[erasure(f)]` mentions a function `f` from `core` or `std`, you must use
`-Zbuild-std` to get access to their THIR. Also make sure to have `rust-src` in your toolchain.

```
rustup component add rust-src --toolchain $MY_TOOLCHAIN
```

### Private functions

It is also possible to name a private function using the `private` keyword
followed by the full path to the private function:

```rust
#[erasure(private crate_name::path::to::f)]
```

### Nested functions

`#[erasure]` automatically takes nested functions into account.

```rust
fn f() {
  fn inside_f() {}
  inside_f()
}

#[erasure(f)]
fn g() {
  fn inside_f() {}
  inside_f()
}
```

The inner function of `g` does not need an `#[erasure]` attribute,
but it must have the same name as its counterpart in `f`.

### Ghost functions

Ghost functions are those that may appear outside of ghost blocks
but are completely eraseable. The main examples are [`Ghost::split`][ghost-split]
and [`Ghost::borrow`][ghost-borrow]. They are identified by the attribute `#[erasure(_)]`.

[ghost-split]: https://creusot-rs.github.io/creusot/doc/creusot_contracts/ghost/struct.Ghost.html#method.split
[ghost-borrow]: https://creusot-rs.github.io/creusot/doc/creusot_contracts/ghost/struct.Ghost.html#method.borrow

```rust
#[trusted]
#[erasure(_)]
fn split<T, U>(g: Ghost<(T, U)>) -> (Ghost<T>, Ghost<U>) { /* ... */ }
```
