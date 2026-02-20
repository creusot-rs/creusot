# Loop invariants

> [!NOTE]
>
> The word "invariant" has a lot of different meanings in program verification.
> Even within Creusot, there are at least three unrelated meanings,
> and we avoid ambiguity by always qualifying the noun "invariant" accordingly:
>
> - Loop invariants, discussed in this chapter.
> - [Type invariants](../type_invariants).
> - Resource invariants, for separation logic reasoning about shared resources.
>   In Creusot, we further distinguish "atomic invariants" and "non-atomic invariants";
>   see the module [`creusot_std::ghost::invariant`](https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/invariant/index.html).

When writing a loop (be it `for`, `while` or `loop`), you will generally need to specify a **loop invariant**,
that is an assertion that stays true for the duration of the loop.

For example, consider the following program:

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

This program needs a loop invariant: even though its proof seems obvious to us, it is not for Creusot. What Creusot knows is:

- Any variable not referenced in the loop is unchanged at the end (here this is obvious because `n` is immutable, but it might be relevant in a more complicated program).
- At the end of the loop, the loop condition is false: here `total >= n`.

We still need to know that `total <= n` to get `result == n`.
Use the [`#[invariant]`](https://creusot-rs.github.io/creusot/doc/creusot_std/macros/attr.invariant.html)
attribute to write loop invariants:

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

The reason why loop invariants are useful is that they enable reducing the verification problem
to verifying loop-free fragments of code.

For example, consider a function with one `while` loop:

```rust
#[requires(PRE)]
#[ensures(POST(result))]
fn f(x: A) -> B {
    CODE_BEFORE_LOOP;
    #[invariant(INVARIANT)]
    while CONDITION {
        LOOP_BODY;
    }
    CODE_AFTER_LOOP
}
```

To prove that this function satisfies its contract, we only have to verify three simpler subprograms
(here in pseudo-code).

1. The code before the loop must establish the invariant, assuming the precondition.

    ```rust
    assume! { PRE }
    CODE_BEFORE_LOOP;
    assert! { INVARIANT }
    ```

2. The loop body must preserve the invariant, assuming that the loop condition is `true`.

    ```rust
    assume! { INVARIANT && CONDITION }
    LOOP_BODY
    assert! { INVARIANT }
    ```

3. The code after the loop must establish the postcondition, assuming that the invariant holds and the loop condition is `false`.

    ```rust
    assume! { INVARIANT && !CONDITION }
    let result = { CODE_AFTER_LOOP };
    assert! { POST(result) }
    ```

If you don't provide a loop invariant, it defaults to `true`, and you are left with very
little information to reason about the loop body and the code after the loop.

Note that this is an oversimplified example. As mentioned in the previous section,
facts about variables that are not referenced by the loop body are automatically
preserved and don't need to be mentioned explicitly in the invariant.

## `for` loop invariants: `produced`

Invariants of `for` loops have access to a special `produced` variable which
contains the sequence of elements produced by the iterator, in a snapshot.

```rust
#[invariant(I)]
for PAT in ITER {
   BODY
}
```

The above desugars to the following, where `produced` is explicitly defined and in scope in `I`:

```rust
let mut it = ::std::iter::IntoIterator::into_iter(ITER);
let iter_old = snapshot! { it };
let mut produced = snapshot! { ::creusot_std::logic::Seq::empty() };
#[invariant(I)]
loop {
    match ::std::iter::Iterator::next(&mut it) {
        Some(elem) => {
            produced = snapshot! { produced.inner().concat(::creusot_std::logic::Seq::singleton(elem)) };
            let PAT = elem;
            BODY
        },
        None => break,
    }
}
```

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
