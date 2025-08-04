# Ghost structures

## Using imperative data structures in ghost code

Usual imperative structures like `Vec`, `HashMap` or `HashSet` cannot be used in ghost code. To be precise, you may notice that functions like `Vec::push` are not marked with the `#[check(ghost)]` attribute, and so they cannot be called in ghost code.

This is because this function (and other like it) allocate memory, which on the actual machine, is finite. This currently translates to a possible inconsistency when using `Vec` in ghost code:

```rust
use creusot_contracts::{proof_assert, ghost};
ghost! {
    let mut v = Vec::new();
    for _ in 0..=usize::MAX as u128 + 1 {
        v.push(0);
    }
    proof_assert!(v@.len() <= usize::MAX@); // by definition
    proof_assert!(v@.len() > usize::MAX@);  // uh-oh
}
```

This case might be forbidden in the future by adding a stronger precondition to `Vec::push`, but the point still stands: the capacity of a ghost vector should be infinite.

## Ghost structures

As such, ghost code uses the mathematical structures `Seq`, `FMap` and `FSet`, and adds program functions onto them.

The above snippet becomes:

```rust
use creusot_contracts::{proof_assert, ghost, Int, logic::Seq};
ghost! {
    let mut s: Seq<Int> = Seq::new();
    for _ in 0..=usize::MAX as u128 + 1 {
        s.push_ghost(0);
    }
    // proof_assert!(s.len() <= usize::MAX@); // fails
    proof_assert!(s.len() > usize::MAX@);
}
```

A few things to note:

- `Seq`, `FMap` and `FSet` are the counterparts for `Vec`, `HashMap` and `HashSet` respectively. They all live in the `logic` module.
- Since `s` in directly the logical type `Seq`, we don't need the view operator `@`.
- To avoid name clashes, these additional "ghost" functions are almost all suffixed with `_ghost`. See the documentation for each type to know the available methods, ghost and logical.
