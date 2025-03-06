# Invariants

When writing a loop (be it `for`, `while` or `loop`), you will generally need to specify an **invariant**, that is an assertion that stays true for the duration of the loop. For example, the following program:

```rust
#[ensures(result == n)]
fn loop_add(n: u64) -> u64 {
    let mut total = 0;
    while total < n {
        total += 1;
    }
    total
}
```

Needs an invariant: even though its proof seems obvious to us, it is not for Creusot. What Creusot knows is:

- Any variable not referenced in the loop is unchanged at the end (here this is obvious because `n` is immutable, but it might be relevant in a more complicated program).
- At the end of the loop, the loop condition is false: here `total >= n`.

We still need to know that `total <= n` to get `result == n`:

```rust
#[ensures(result == n)]
fn loop_add(n: u64) -> u64 {
    let mut total = 0;
    #[invariant(total <= n)]
    while total < n {
        total += 1;
    }
    total
}
```

This is now provable !

> Like `requires` and `ensures`, `invariant` must contain a pearlite expression returning a boolean.

## Verification conditions

An `invariant` generates two verification conditions in Why3:

- First, that the invariants holds before the loop (initialization).
- Second, that if the invariant holds at the beginning of a loop iteration, then it holds at the end of it.

## Compiling with `rustc`

Make sure that functions that contain `#[invariant(...)]` attributes also have
an `#[ensures(...)]` or `#[requires(...)]` attribute.
You can always add `#[ensures(true)]` as a trivial contract.

That enables compilation (`cargo build`) with a stable Rust compiler,
preventing the following error:

```
error[E0658]: attributes on expressions are experimental
```

Indeed, the `#[invariant(...)]` attribute on loops is only allowed by unstable features
(`stmt_expr_attributes`, `proc_macro_hygiene`). For compatibility with stable Rust,
the `requires` and `ensures` macros remove `#[invariant(...)]`
attributes during normal compilation.
